import Polyfold.Chapter8.Basic
import Polyfold.Chapter7.NaturalRepFinite

set_option maxSynthPendingDepth 3

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2017, arXiv 1707.08941), Part II,
Chapter 8, §8.4: **Theorem 8.5 (Proper Covering I)** with its proof and **Remark 8.2**,
pp. 277–279.  Proper covering functors (Definition 8.8, p. 275) are
`EpFunctor.IsProperCovering` (`Polyfold/Chapter8/Basic.lean`).  There is no 2014 preprint of
Part II; numbers and pages are the 2017 text's.

# Proper Covering I: a proper covering functor near a fibre

## The text, paraphrased

(Theorem 8.5, p. 277) Let `F : Y → X` be a proper covering functor and `x ∈ X`.  For a connected
and sufficiently small open neighbourhood `U(x)` admitting the natural `G_x`-action (the data
`(Φ, Γ)` of Theorem 7.1): (0) `F⁻¹(U(x))` is a disjoint union of connected open neighbourhoods
`U(y)`, `y ∈ F⁻¹(x)`, with every `F : U(y) → U(x)` an sc-diffeomorphism; (1) `Γ(G_x, U(x)) =
{φ ∈ 𝐗 | s(φ), t(φ) ∈ U(x)} =: 𝐔(x)` is the union of the connected components `𝐔(g)`, `g ∈ G_x`,
and `s, t : 𝐔(g) → U(x)` are sc-diffeomorphisms; (2) for `y, y' ∈ F⁻¹(x)` the set
`𝐔(y, y') = {ψ ∈ 𝐘 | s(ψ) ∈ U(y), t(ψ) ∈ U(y')}` is the disjoint union of connected open
neighbourhoods `𝐔(ψ₀)` centred at the morphisms `ψ₀ : y → y'`, for which (3) `s : 𝐔(ψ₀) → U(y)`
and `t : 𝐔(ψ₀) → U(y')` are sc-diffeomorphisms, (4) `F : 𝐔(ψ₀) → 𝐔(F(ψ₀))` is an
sc-diffeomorphism, and (5) the square with top arrow `F : 𝐔(ψ₀) → 𝐔(F(ψ₀))`, left arrow `s`,
right arrow `t`, bottom arrow `F : U(s(ψ₀)) → U(t(F(ψ₀)))` is a commutative diagram of
sc-diffeomorphisms.

(Remark 8.2, p. 277) (a) Since `F` is a functor, for `φ : y → y'` with `y, y' ∈ F⁻¹(x)` the
morphism `F(φ) : F(y) → F(y')` belongs to `G_x`.  (b) In Theorem 8.5 everything is determined
by the choice of a small connected open `U(x)` admitting the natural `G_x`-action; the
construction of `(Φ, Γ)` is natural (Theorem 7.1); the main point of the proof is the interplay
of `F` with `s` and `t` given by functoriality.

(Proof, pp. 278–279) `A = F⁻¹(x)` is finite, and for a connected open `U'(x)` the preimage
`F⁻¹(U'(x))` is the disjoint union of connected open `U'(y)` with `F : U'(y) → U'(x)`
sc-diffeomorphisms (Definition 8.8); one may assume `U'(x)` admits the natural `G_x`-action.
Around `y ∈ A` take connected open `V(y) ⊆ U'(y)` admitting the natural `G_y`-action and for
`ψ : y → y'` connected open `V(ψ)` with `s : V(ψ) → V(y)`, `t : V(ψ) → V(y')`
sc-diffeomorphisms; `ψ̂ = t ∘ (s|V(ψ))⁻¹ : V(y) → V(y')` (8.15); the morphisms between points of
`⋃ V(y)` form the disjoint union of the `V(ψ)`.  Take a smaller `G_x`-invariant connected open
`U(x) ⊆ U'(x)` with `(F|V(y))⁻¹(U(x)) ⊆ V(y)` and put `U(y) = (F|V(y))⁻¹(U(x))`.  Then `ψ̂` maps
`U(y)` onto `U(y')`: for `z ∈ U(y)`, `z' = ψ̂(z)` and `φ : z → z'`, `F(φ) = Γ(g, F(z))` for some
`g`, so `F(z') ∈ U(x)` by invariance.  With `𝐔(ψ) = (s|V(ψ))⁻¹(U(y))` this gives (0)–(3).  For
(4): `F(ψ₀) = g ∈ G_x`, `F(𝐔(ψ₀)) ⊆ 𝐔(g)` since `𝐔(ψ₀)` is connected, and
`F = (s|𝐔(g))⁻¹ ∘ F ∘ s` on `𝐔(ψ₀)`; (5) is then obvious.

## What is formalized

* **Remark 8.2 (a)**: `EpFunctor.remark_8_2_a` (`F(φ) ∈ mor(x, x)`) and the element
  `EpFunctor.isotropyMor : G_x` it defines.
* `EpFunctor.ProperCoveringChart F x`: a natural representation `R` of `G_x` (`R.U = U(x)`,
  `R.Φ`, `R.Γ`), the sets `U(y)` and `𝐔(ψ₀)`, and the properties (0)–(5) as fields.
* **Theorem 8.5**: `EpFunctor.theorem_8_5` (a chart with `U(x)` inside any given open `V ∋ x`) and
  `EpFunctor.theorem_8_5_of_naturalRep` (the "for every sufficiently small" form: there is an open
  `W ∋ x` such that every natural representation of `G_x` on some `U(x) ⊆ W` is the `R` of a
  chart).
* **Remark 8.2 (b)**, as far as it has formal content: `ProperCoveringChart.connectedComponentIn_U`
  (`U(y)` is the connected component of `F⁻¹(U(x))` at `y`),
  `ProperCoveringChart.connectedComponentIn_sheet` (`𝐔(ψ₀)` is the connected component of
  `𝐔(s ψ₀, t ψ₀)` at `ψ₀`), and `EpFunctor.remark_8_2_b`: two charts with the same `U(x)` have the
  same `Φ` and `Γ` on `U(x)`, the same `U(y)` and the same `𝐔(ψ₀)`.
* The construction (namespace `EpFunctor.ProperCoveringLocal`): `Data` (the input from Definition
  8.8 and a natural representation), the sections `Data.τ`, the sets `Data.U`, `Data.sheet`, and
  `Data.toChart`; general facts `isScSmoothOn_of_section` (a continuous section of `s` over an open
  set is sc-smooth), `mapsTo_of_isPreconnected`, `connectedComponentIn_eq_of_iUnion`,
  `isScDiffeoOn_congr_left`.

## What the text leaves implicit, and the choices made

* **"Sufficiently small"**.  `theorem_8_5` reads it as "inside any given open `V ∋ x`".  The proof
  uses only `U(x) ⊆ U'(x)` for the `U'(x)` of Definition 8.8 (2), so the stronger reading also
  holds: `theorem_8_5_of_naturalRep` gives one open `W ∋ x` that works for every natural
  representation on a connected `U(x) ⊆ W`.  "Connected, admitting the natural `G_x`-action" is
  `R : X.NaturalRep x` (Chapter 7's structure, whose `U` is open and connected).
* **"Disjoint union of connected open neighbourhoods"** means: each set is open, connected and
  contains its centre, the sets are pairwise disjoint over the index set, and their union is the
  given set.  The index sets are `F⁻¹(x)` for the `U(y)` and `Y.morOn (F⁻¹(x))`, the morphisms
  between points of `F⁻¹(x)`, for the `𝐔(ψ₀)`; `U` and `sheet` are functions on all objects and
  morphisms, with no condition off the index sets.  That these sets are then the connected
  components is `connectedComponentIn_U`, `connectedComponentIn_sheet`.
* **`𝐔(g)` and `𝐔(F(ψ₀))`**.  For `φ ∈ 𝐔(x)` the set `𝐔(φ)` is read as the connected component
  `connectedComponentIn (X.morOn U(x)) φ` of `𝐔(x)` containing `φ`; by Remark 8.2 (a)
  `F(ψ₀) ∈ 𝐔(x)`, and (1) identifies `𝐔(g)` with the sheet `Γ(g, U(x))`.  Part (1) involves
  only `(U(x), Φ, Γ)`; it is Chapter 7's `NaturalRep.bijOn_Γ`, `iUnion_image_Γ`,
  `pairwise_disjoint_image_Γ`, `connectedComponentIn_morOn`, `isScDiffeoOn_src_image`,
  `isScDiffeoOn_tgt_image` (`Polyfold/Chapter7/NaturalAction.lean`), restated in the fields.
* **"`s : 𝐔(ψ₀) → U(y)` is an sc-diffeomorphism"** is `∃ σ, IsScDiffeoOn s σ (𝐔 ψ₀) (U y)`
  (Part I's sc-diffeomorphism between open subsets, with an inverse), and likewise for the others.
* **(5), a possible misprint.**  As printed, the right vertical arrow is `t` and the lower right
  corner is `U(t(F(ψ₀)))`.  With `t` the square says `F(s(ψ)) = t(F(ψ))` on `𝐔(ψ₀)`, which does not
  hold as we read it: a functor gives `F(s(ψ)) = s(F(ψ))`, while `F(ψ) = Γ(g, F(s ψ))` with
  `g = F(ψ₀)` has `t(F(ψ)) = Φ(g)(F(s ψ))`, different from `s(F(ψ))` wherever `Φ(g)` does not fix
  `F(s ψ)`.  We formalize the square with `s` on both sides (`comm_src`; the
  corner `U(s(F(ψ₀))) = U(x)` is the same set, as `s(F(ψ₀)) = t(F(ψ₀)) = x`) and the companion
  square with `t` on both sides (`comm_tgt`: `F(t(ψ)) = t(F(ψ))`, over `F : U(t ψ₀) → U(x)`).  "Of
  sc-diffeomorphisms": the left arrows are (3), the top arrow (4), the bottom arrows (0) at
  `y = s ψ₀` and `y = t ψ₀`, and the right arrows `s, t : 𝐔(F(ψ₀)) → U(x)` the fields
  `isScDiffeoOn_src_sheetF`, `isScDiffeoOn_tgt_sheetF`.
* **Possible misprints in the proof** (p. 278), as we read it: "there exists `g ∈ G_y` for which
  `F(φ) = Γ(g, F(z))`" — `Γ` is the natural representation of `G_x` on `U'(x)`, so `g ∈ G_x` is
  meant; "`U(x)` is a `G_y`-invariant subset of `U'(x)`" — `G_x`-invariant is meant; "`F(z') =
  s(F(φ))`" — for `φ : z → z'`, `F(z') = t(F(φ))` is meant.
* **The route of the proof.**  The text decomposes the morphisms of `𝐘` near `F⁻¹(x)` by sheets
  `V(ψ)` and natural representations of the `G_y` in `Y` (a construction in the manner of
  Proposition 7.5), and Definition 8.8 (3) is not invoked.  Here condition (3) of Definition 8.8
  does that work: `L = (F, s) : 𝐘 → 𝐗 ₛ×_F Y` is a bijection with continuous inverse, and for
  `ψ₀ : y → y'` with `g = F(ψ₀)` we put `τ(z) = L⁻¹(Γ(g, F(z)), z)` and `𝐔(ψ₀) = τ(U(y))`, where
  `U(y) = U'(y) ∩ F⁻¹(U(x))`.  `τ` is a continuous section of `s`, hence sc-smooth
  (`isScSmoothOn_of_section`); `t ∘ τ = (F|U(y'))⁻¹ ∘ Φ(g) ∘ F` maps `U(y)` into `U(y')` because
  `U(y)` is connected and `F⁻¹(U(x))` is the disjoint union of the open `U(y'')`
  (`Data.tgt_τ_mem`, the counterpart of the text's claim that `ψ̂` maps `U(y)` onto `U(y')`); and
  `F = Γ(g, ·) ∘ F ∘ s` on `𝐔(ψ₀)` (`Data.isScDiffeoOn_mor_sheet`) is the text's formula for (4).
  The finiteness of `F⁻¹(x)` and condition (1) of Definition 8.8 are not needed.
* **Remark 8.2 (b)** is read as: given `U(x)`, the data `Φ`, `Γ` on `U(x)` (on a connected `U(x)`,
  `Γ(g, ·)` is the continuous section of `s` through `g`, `NaturalRep.Γ_eqOn`), the `U(y)` and the
  `𝐔(ψ₀)` are determined (`remark_8_2_b`).  Its remarks on the naturality of Theorem 7.1's
  construction and on the main point of the proof have no further formal content.
-/

open Set Function Topology

noncomputable section

namespace Polyfold

universe u v

namespace EpFunctor

namespace ProperCoveringLocal

/-! ### General facts -/

section General

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}

/-- An sc-diffeomorphism `U → V` stays one when the map is changed on `U` only. -/
theorem isScDiffeoOn_congr_left {f f' : X → Y} {g : Y → X} {U : Set X} {V : Set Y}
    (h : P.IsScDiffeoOn Q f g U V) (hff' : EqOn f f' U) : P.IsScDiffeoOn Q f' g U V where
  isScSmoothOn := h.isScSmoothOn.congr hff'
  isScSmoothOn_inv := h.isScSmoothOn_inv
  mapsTo z hz := by rw [← hff' hz]; exact h.mapsTo hz
  mapsTo_inv := h.mapsTo_inv
  left_inv z hz := by rw [← hff' hz]; exact h.left_inv z hz
  right_inv w hw := by rw [← hff' (h.mapsTo_inv hw)]; exact h.right_inv w hw

end General

/-- A continuous map on a preconnected set with values in a union of pairwise disjoint open sets
`W i` takes all its values in the `W i₀` containing one of them. -/
theorem mapsTo_of_isPreconnected {α β ι : Type*} [TopologicalSpace α] [TopologicalSpace β]
    {S : Set α} (hS : IsPreconnected S) {f : α → β} (hf : ContinuousOn f S) {I : Set ι}
    {W : ι → Set β} (hWo : ∀ i ∈ I, IsOpen (W i)) (hW : I.PairwiseDisjoint W)
    (hfS : MapsTo f S (⋃ i ∈ I, W i)) {z₀ : α} (hz₀ : z₀ ∈ S) {i₀ : ι} (hi₀ : i₀ ∈ I)
    (h₀ : f z₀ ∈ W i₀) : MapsTo f S (W i₀) := by
  have key := (hS.image f hf).subset_left_of_subset_union (hWo i₀ hi₀)
    (v := ⋃ i ∈ I \ {i₀}, W i) (isOpen_biUnion fun i hi => hWo i hi.1)
    (disjoint_iUnion₂_right.2 fun i hi => hW hi₀ hi.1 (Ne.symm hi.2)) ?_
    ⟨f z₀, mem_image_of_mem f hz₀, h₀⟩
  · exact fun z hz => key (mem_image_of_mem f hz)
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨i, hi, hfi⟩ := mem_iUnion₂.1 (hfS hz)
    by_cases hii : i = i₀
    · subst hii
      exact Or.inl hfi
    · exact Or.inr (mem_iUnion₂.2 ⟨i, ⟨hi, hii⟩, hfi⟩)

/-- If a set is the union of pairwise disjoint connected open sets `W i`, these are its connected
components. -/
theorem connectedComponentIn_eq_of_iUnion {β ι : Type*} [TopologicalSpace β] {I : Set ι}
    {W : ι → Set β} (hWo : ∀ i ∈ I, IsOpen (W i)) (hWc : ∀ i ∈ I, IsConnected (W i))
    (hW : I.PairwiseDisjoint W) {i₀ : ι} (hi₀ : i₀ ∈ I) {a : β} (ha : a ∈ W i₀) :
    connectedComponentIn (⋃ i ∈ I, W i) a = W i₀ := by
  have hsub : W i₀ ⊆ ⋃ i ∈ I, W i := subset_biUnion_of_mem (u := W) hi₀
  refine Subset.antisymm ?_ ((hWc i₀ hi₀).isPreconnected.subset_connectedComponentIn ha hsub)
  have h := mapsTo_of_isPreconnected (f := _root_.id) isPreconnected_connectedComponentIn
    continuousOn_id hWo hW (fun b hb => connectedComponentIn_subset _ _ hb)
    (mem_connectedComponentIn (hsub ha)) hi₀ ha
  exact fun b hb => h hb

section Groupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- **A continuous section of `s` over an open set is sc-smooth** there: near each point it is
the inverse of `s` on a set where `s` is an sc-diffeomorphism. -/
theorem isScSmoothOn_of_section {U : Set Obj} (hU : IsOpen U) {τ : Obj → Mor}
    (hτ : ContinuousOn τ U) (hsec : ∀ z ∈ U, X.src (τ z) = z) :
    X.PObj.IsScSmoothOn X.PMor τ U := by
  refine MPolyfold.IsScSmoothOn.of_locally hU fun z hz => ?_
  obtain ⟨W, W', h, hW, hd⟩ := X.isLocalScDiffeo_src (τ z)
  have hN : IsOpen (U ∩ τ ⁻¹' W ∩ W') :=
    (hτ.isOpen_inter_preimage hU hd.isOpen_source).inter hd.isOpen_target
  refine ⟨U ∩ τ ⁻¹' W ∩ W', hN, ⟨⟨hz, hW⟩, ?_⟩, fun w hw => hw.1.1, ?_⟩
  · rw [← hsec z hz]
    exact hd.mapsTo hW
  · refine (hd.isScSmoothOn_inv.mono hN inter_subset_right).congr fun w hw => ?_
    have h1 := hd.left_inv (τ w) hw.1.2
    rwa [hsec w hw.1.1] at h1

variable {X}

/-- The connected component of `𝐔(x)` at `g ∈ G_x` is the sheet `Γ(g, U(x))`
(`NaturalRep.connectedComponentIn_morOn`). -/
theorem connectedComponentIn_morOn_val {x : Obj} (R : X.NaturalRep x) (g : X.Isotropy x) :
    connectedComponentIn (X.morOn R.U) g.val = R.Γ g '' R.U :=
  R.connectedComponentIn_morOn ⟨x, R.mem_U, R.Γ_self g⟩

end Groupoid

end ProperCoveringLocal

variable {ObjY MorY : Type u} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  {ObjX MorX : Type v} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {Y : EpGroupoid ObjY MorY} {X : EpGroupoid ObjX MorX}

/-! ### Remark 8.2 (a) -/

/-- **Remark 8.2 (a)**: since `F` is a functor, a morphism `φ : y → y'` between points `y, y'` of
`F⁻¹(x)` is mapped to a morphism `F(φ) : x → x`, an element of the isotropy group `G_x`. -/
theorem remark_8_2_a (F : EpFunctor Y X) {x : ObjX} {φ : MorY}
    (hφ : φ ∈ Y.morOn (F.obj ⁻¹' {x})) : F.mor φ ∈ X.mor x x :=
  ⟨(F.src_mor φ).trans hφ.1, (F.tgt_mor φ).trans hφ.2⟩

/-- The element `F(φ) ∈ G_x` of Remark 8.2 (a). -/
def isotropyMor (F : EpFunctor Y X) {x : ObjX} {φ : MorY} (hφ : φ ∈ Y.morOn (F.obj ⁻¹' {x})) :
    X.Isotropy x :=
  ⟨F.mor φ, (F.remark_8_2_a hφ).1, (F.remark_8_2_a hφ).2⟩

@[simp]
theorem isotropyMor_val (F : EpFunctor Y X) {x : ObjX} {φ : MorY}
    (hφ : φ ∈ Y.morOn (F.obj ⁻¹' {x})) : (F.isotropyMor hφ).val = F.mor φ := rfl

/-! ### The statement of Theorem 8.5 -/

/-- **The conclusion of Theorem 8.5** for `F : Y → X` at `x ∈ X`: a natural representation
`R = (U(x), Φ, Γ)` of `G_x` (Theorem 7.1; `U(x)` open and connected), open sets `U(y)` for
`y ∈ F⁻¹(x)` and `𝐔(ψ₀)` for the morphisms `ψ₀` between points of `F⁻¹(x)`, with (0)–(5).  For a
morphism `φ ∈ 𝐔(x) = X.morOn U(x)`, `𝐔(φ)` is the connected component
`connectedComponentIn (X.morOn U(x)) φ` of `𝐔(x)` at `φ`; it is `𝐔(g)` for `φ = g ∈ G_x` and
`𝐔(F(ψ₀))` for `φ = F(ψ₀)` (Remark 8.2 (a)). -/
structure ProperCoveringChart (F : EpFunctor Y X) (x : ObjX) where
  /-- The natural representation `(Φ, Γ)` of `G_x` on the connected open `U(x) = R.U`. -/
  R : X.NaturalRep x
  /-- The neighbourhoods `U(y)`, `y ∈ F⁻¹(x)`. -/
  U : ObjY → Set ObjY
  /-- The neighbourhoods `𝐔(ψ₀)` of the morphisms `ψ₀` between points of `F⁻¹(x)`. -/
  sheet : MorY → Set MorY
  /-- (0) Every `U(y)` is open. -/
  isOpen_U : ∀ y ∈ F.obj ⁻¹' {x}, IsOpen (U y)
  /-- (0) Every `U(y)` is connected. -/
  isConnected_U : ∀ y ∈ F.obj ⁻¹' {x}, IsConnected (U y)
  /-- (0) `U(y)` is a neighbourhood of `y`. -/
  mem_U : ∀ y ∈ F.obj ⁻¹' {x}, y ∈ U y
  /-- (0) The `U(y)` are mutually disjoint. -/
  pairwiseDisjoint_U : (F.obj ⁻¹' {x}).PairwiseDisjoint U
  /-- (0) The union of the `U(y)` is `F⁻¹(U(x))`. -/
  preimage_eq : F.obj ⁻¹' R.U = ⋃ y ∈ F.obj ⁻¹' {x}, U y
  /-- (0) Every `F : U(y) → U(x)` is an sc-diffeomorphism. -/
  isScDiffeoOn_obj : ∀ y ∈ F.obj ⁻¹' {x},
    ∃ σ : ObjX → ObjY, Y.PObj.IsScDiffeoOn X.PObj F.obj σ (U y) R.U
  /-- (1) `Γ(G_x, U(x)) = 𝐔(x) = {φ ∈ 𝐗 | s(φ), t(φ) ∈ U(x)}`. -/
  image_Γ : (fun p : X.Isotropy x × ObjX => R.Γ p.1 p.2) '' (univ ×ˢ R.U) = X.morOn R.U
  /-- (1) `𝐔(x)` is the union of its connected components `𝐔(g)`, `g ∈ G_x`. -/
  iUnion_sheetX : X.morOn R.U = ⋃ g : X.Isotropy x, connectedComponentIn (X.morOn R.U) g.val
  /-- (1) The `𝐔(g)`, `g ∈ G_x`, are mutually disjoint. -/
  pairwise_disjoint_sheetX :
    Pairwise (Disjoint on fun g : X.Isotropy x => connectedComponentIn (X.morOn R.U) g.val)
  /-- (1) `𝐔(g) = Γ(g, U(x))`. -/
  connectedComponentIn_eq :
    ∀ g : X.Isotropy x, connectedComponentIn (X.morOn R.U) g.val = R.Γ g '' R.U
  /-- (1) `s : 𝐔(g) → U(x)` is an sc-diffeomorphism. -/
  isScDiffeoOn_src_sheetX : ∀ g : X.Isotropy x, ∃ σ : ObjX → MorX,
    X.PMor.IsScDiffeoOn X.PObj X.src σ (connectedComponentIn (X.morOn R.U) g.val) R.U
  /-- (1) `t : 𝐔(g) → U(x)` is an sc-diffeomorphism. -/
  isScDiffeoOn_tgt_sheetX : ∀ g : X.Isotropy x, ∃ σ : ObjX → MorX,
    X.PMor.IsScDiffeoOn X.PObj X.tgt σ (connectedComponentIn (X.morOn R.U) g.val) R.U
  /-- (2) Every `𝐔(ψ₀)` is open. -/
  isOpen_sheet : ∀ ψ₀ ∈ Y.morOn (F.obj ⁻¹' {x}), IsOpen (sheet ψ₀)
  /-- (2) Every `𝐔(ψ₀)` is connected. -/
  isConnected_sheet : ∀ ψ₀ ∈ Y.morOn (F.obj ⁻¹' {x}), IsConnected (sheet ψ₀)
  /-- (2) `𝐔(ψ₀)` is centred at `ψ₀`. -/
  mem_sheet : ∀ ψ₀ ∈ Y.morOn (F.obj ⁻¹' {x}), ψ₀ ∈ sheet ψ₀
  /-- (2) The `𝐔(ψ₀)` are mutually disjoint. -/
  pairwiseDisjoint_sheet : (Y.morOn (F.obj ⁻¹' {x})).PairwiseDisjoint sheet
  /-- (2) `𝐔(y, y') = {ψ ∈ 𝐘 | s(ψ) ∈ U(y), t(ψ) ∈ U(y')}` is the union of the `𝐔(ψ₀)`,
  `ψ₀ : y → y'`. -/
  morOn_U_eq : ∀ y ∈ F.obj ⁻¹' {x}, ∀ y' ∈ F.obj ⁻¹' {x},
    {ψ | Y.src ψ ∈ U y ∧ Y.tgt ψ ∈ U y'} = ⋃ ψ₀ ∈ Y.mor y y', sheet ψ₀
  /-- (3) `s : 𝐔(ψ₀) → U(s ψ₀)` is an sc-diffeomorphism. -/
  isScDiffeoOn_src : ∀ ψ₀ ∈ Y.morOn (F.obj ⁻¹' {x}), ∃ σ : ObjY → MorY,
    Y.PMor.IsScDiffeoOn Y.PObj Y.src σ (sheet ψ₀) (U (Y.src ψ₀))
  /-- (3) `t : 𝐔(ψ₀) → U(t ψ₀)` is an sc-diffeomorphism. -/
  isScDiffeoOn_tgt : ∀ ψ₀ ∈ Y.morOn (F.obj ⁻¹' {x}), ∃ σ : ObjY → MorY,
    Y.PMor.IsScDiffeoOn Y.PObj Y.tgt σ (sheet ψ₀) (U (Y.tgt ψ₀))
  /-- (4) `F : 𝐔(ψ₀) → 𝐔(F(ψ₀))` is an sc-diffeomorphism. -/
  isScDiffeoOn_mor : ∀ ψ₀ ∈ Y.morOn (F.obj ⁻¹' {x}), ∃ G : MorX → MorY,
    Y.PMor.IsScDiffeoOn X.PMor F.mor G (sheet ψ₀) (connectedComponentIn (X.morOn R.U) (F.mor ψ₀))
  /-- (5) The square `F ∘ s = s ∘ F` from `𝐔(ψ₀)` to `U(x)` commutes (the right arrow `t` as
  printed is read as `s`, a possible misprint). -/
  comm_src : ∀ ψ₀ ∈ Y.morOn (F.obj ⁻¹' {x}), ∀ ψ ∈ sheet ψ₀, F.obj (Y.src ψ) = X.src (F.mor ψ)
  /-- (5) The right arrow `s : 𝐔(F(ψ₀)) → U(x)` of that square is an sc-diffeomorphism (its other
  arrows are those of (0), (3), (4)). -/
  isScDiffeoOn_src_sheetF : ∀ ψ₀ ∈ Y.morOn (F.obj ⁻¹' {x}), ∃ σ : ObjX → MorX,
    X.PMor.IsScDiffeoOn X.PObj X.src σ (connectedComponentIn (X.morOn R.U) (F.mor ψ₀)) R.U
  /-- (5) The companion square `F ∘ t = t ∘ F` from `𝐔(ψ₀)` to `U(x)` commutes. -/
  comm_tgt : ∀ ψ₀ ∈ Y.morOn (F.obj ⁻¹' {x}), ∀ ψ ∈ sheet ψ₀, F.obj (Y.tgt ψ) = X.tgt (F.mor ψ)
  /-- (5) The right arrow `t : 𝐔(F(ψ₀)) → U(x)` of the companion square is an sc-diffeomorphism. -/
  isScDiffeoOn_tgt_sheetF : ∀ ψ₀ ∈ Y.morOn (F.obj ⁻¹' {x}), ∃ σ : ObjX → MorX,
    X.PMor.IsScDiffeoOn X.PObj X.tgt σ (connectedComponentIn (X.morOn R.U) (F.mor ψ₀)) R.U

/-! ### The construction -/

namespace ProperCoveringLocal

/-- **The input of the construction**: a natural representation `R` of `G_x` on `U(x) ⊆ U₀`,
where `U₀ = U'(x)` and `V₀(y) = U'(y)`, `y ∈ F⁻¹(x)`, are as in Definition 8.8 (2) with local
inverses `σ y : U₀ → V₀(y)` of `F`, and the inverse `Linv` of `L : φ ↦ (F(φ), s(φ))`, continuous
(Definition 8.8 (3)). -/
structure Data (F : EpFunctor Y X) (x : ObjX) where
  /-- The natural representation on `U(x)`. -/
  R : X.NaturalRep x
  /-- `U'(x)`. -/
  U₀ : Set ObjX
  /-- `U'(y)`. -/
  V₀ : ObjY → Set ObjY
  /-- The inverses of `F : U'(y) → U'(x)`. -/
  σ : ObjY → ObjX → ObjY
  /-- The inverse of `L = (F, s) : 𝐘 → 𝐗 ₛ×_F Y`. -/
  Linv : MPolyfold.fibredProduct X.src F.obj → MorY
  R_subset : R.U ⊆ U₀
  pairwiseDisjoint_V₀ : (F.obj ⁻¹' {x}).PairwiseDisjoint V₀
  mem_V₀ : ∀ y ∈ F.obj ⁻¹' {x}, y ∈ V₀ y
  isScDiffeoOn_σ : ∀ y ∈ F.obj ⁻¹' {x}, Y.PObj.IsScDiffeoOn X.PObj F.obj (σ y) (V₀ y) U₀
  preimage_U₀ : F.obj ⁻¹' U₀ = ⋃ y ∈ F.obj ⁻¹' {x}, V₀ y
  continuous_Linv : Continuous Linv
  Linv_fibredMap : ∀ ψ, Linv (F.fibredMap ψ) = ψ
  fibredMap_Linv : ∀ p, F.fibredMap (Linv p) = p

/-- `F` is continuous on objects. -/
theorem continuous_obj (F : EpFunctor Y X) : Continuous F.obj :=
  continuousOn_univ.1 F.isScSmoothMap_obj.continuousOn

/-- **A proper covering functor provides the input** for every natural representation `R` of
`G_x` on `U(x) ⊆ U'(x)`, `U'(x)` the open set of Definition 8.8 (2). -/
theorem exists_data {F : EpFunctor Y X} (hF : F.IsProperCovering) (x : ObjX) :
    ∃ W : Set ObjX, IsOpen W ∧ x ∈ W ∧
      ∀ R : X.NaturalRep x, R.U ⊆ W → ∃ D : Data F x, D.R = R := by
  obtain ⟨U₀, V₀, σ, hU₀o, hxU₀, hdisj, hV₀, hpre⟩ := hF.evenlyCovered x
  let := MPolyfold.paracompactSpace_prod X.PMor Y.PObj
  let := (X.PMor.prod Y.PObj).paracompactSpace_subtype (MPolyfold.fibredProduct X.src F.obj)
  obtain ⟨Linv, hL⟩ := hF.isScDiffeo_fibredMap
  refine ⟨U₀, hU₀o, hxU₀, fun R hR => ⟨
    { R := R
      U₀ := U₀
      V₀ := V₀
      σ := σ
      Linv := Linv
      R_subset := hR
      pairwiseDisjoint_V₀ := hdisj
      mem_V₀ := fun y hy => (hV₀ y hy).1
      isScDiffeoOn_σ := fun y hy => (hV₀ y hy).2
      preimage_U₀ := hpre
      continuous_Linv := continuousOn_univ.1 hL.isScSmoothOn_inv.continuousOn
      Linv_fibredMap := fun ψ => hL.left_inv ψ (mem_univ _)
      fibredMap_Linv := fun p => hL.right_inv p (mem_univ _) }, rfl⟩⟩

namespace Data

variable {F : EpFunctor Y X} {x : ObjX} (D : Data F x)

/-- `U(y) = V₀(y) ∩ F⁻¹(U(x)) = (F|U'(y))⁻¹(U(x))`. -/
def U (y : ObjY) : Set ObjY := D.V₀ y ∩ F.obj ⁻¹' D.R.U

/-- The sheet index in `G_x` of `F(ψ₀)`; it is `F(ψ₀)` itself for `ψ₀` over `x` (`val_g`). -/
def g (ψ₀ : MorY) : X.Isotropy x := D.R.index (F.mor ψ₀)

open scoped Classical in
/-- The section `τ_{ψ₀}(z) = L⁻¹(Γ(g, F(z)), z)` of `s` over `F⁻¹(U(x))`, `g = F(ψ₀)` (a junk
value off `F⁻¹(U(x))`). -/
def τ (ψ₀ : MorY) (z : ObjY) : MorY :=
  if h : X.src (D.R.Γ (D.g ψ₀) (F.obj z)) = F.obj z then
    D.Linv ⟨(D.R.Γ (D.g ψ₀) (F.obj z), z), h⟩
  else Y.unit z

/-- `𝐔(ψ₀) = τ_{ψ₀}(U(s ψ₀))`. -/
def sheet (ψ₀ : MorY) : Set MorY := D.τ ψ₀ '' D.U (Y.src ψ₀)

variable {D}

/-! #### The neighbourhoods `U(y)` -/

theorem U_subset (y : ObjY) : D.U y ⊆ F.obj ⁻¹' D.R.U := inter_subset_right

theorem isOpen_U {y : ObjY} (hy : y ∈ F.obj ⁻¹' {x}) : IsOpen (D.U y) :=
  (D.isScDiffeoOn_σ y hy).isOpen_source.inter (D.R.isOpen_U.preimage (continuous_obj F))

theorem image_σ {y : ObjY} (hy : y ∈ F.obj ⁻¹' {x}) : D.σ y '' D.R.U = D.U y := by
  have h := D.isScDiffeoOn_σ y hy
  refine Subset.antisymm ?_ fun z hz => ⟨F.obj z, hz.2, h.left_inv z hz.1⟩
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨h.mapsTo_inv (D.R_subset hw), by
    rw [mem_preimage, h.right_inv w (D.R_subset hw)]; exact hw⟩

theorem isConnected_U {y : ObjY} (hy : y ∈ F.obj ⁻¹' {x}) : IsConnected (D.U y) := by
  rw [← image_σ hy]
  exact D.R.isConnected_U.image _
    ((D.isScDiffeoOn_σ y hy).isScSmoothOn_inv.continuousOn.mono D.R_subset)

theorem mem_U {y : ObjY} (hy : y ∈ F.obj ⁻¹' {x}) : y ∈ D.U y := by
  refine ⟨D.mem_V₀ y hy, ?_⟩
  change F.obj y ∈ D.R.U
  rw [show F.obj y = x from hy]
  exact D.R.mem_U

/-- `F : U(y) → U(x)` is an sc-diffeomorphism, with inverse `σ y`. -/
theorem isScDiffeoOn_U {y : ObjY} (hy : y ∈ F.obj ⁻¹' {x}) :
    Y.PObj.IsScDiffeoOn X.PObj F.obj (D.σ y) (D.U y) D.R.U := by
  have h := D.isScDiffeoOn_σ y hy
  exact
    { isScSmoothOn := h.isScSmoothOn.mono (isOpen_U hy) inter_subset_left
      isScSmoothOn_inv := h.isScSmoothOn_inv.mono D.R.isOpen_U D.R_subset
      mapsTo := fun z hz => hz.2
      mapsTo_inv := fun w hw => ⟨h.mapsTo_inv (D.R_subset hw), by
        rw [mem_preimage, h.right_inv w (D.R_subset hw)]; exact hw⟩
      left_inv := fun z hz => h.left_inv z hz.1
      right_inv := fun w hw => h.right_inv w (D.R_subset hw) }

theorem pairwiseDisjoint_U : (F.obj ⁻¹' {x}).PairwiseDisjoint D.U :=
  D.pairwiseDisjoint_V₀.mono fun _ => inter_subset_left

theorem preimage_eq : F.obj ⁻¹' D.R.U = ⋃ y ∈ F.obj ⁻¹' {x}, D.U y := by
  refine Subset.antisymm (fun z hz => ?_) (iUnion₂_subset fun y _ => U_subset y)
  have hz' : z ∈ F.obj ⁻¹' D.U₀ := D.R_subset hz
  rw [D.preimage_U₀] at hz'
  obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.1 hz'
  exact mem_iUnion₂.2 ⟨y, hy, hzy, hz⟩

/-! #### The sections `τ_{ψ₀}` -/

theorem src_Γ_obj (ψ₀ : MorY) {z : ObjY} (hz : F.obj z ∈ D.R.U) :
    X.src (D.R.Γ (D.g ψ₀) (F.obj z)) = F.obj z :=
  D.R.src_Γ _ _ hz

theorem τ_eq (ψ₀ : MorY) {z : ObjY} (hz : F.obj z ∈ D.R.U) :
    D.τ ψ₀ z = D.Linv ⟨(D.R.Γ (D.g ψ₀) (F.obj z), z), src_Γ_obj ψ₀ hz⟩ := by
  rw [τ, dif_pos (src_Γ_obj ψ₀ hz)]

theorem fibredMap_τ (ψ₀ : MorY) {z : ObjY} (hz : F.obj z ∈ D.R.U) :
    F.fibredMap (D.τ ψ₀ z) = ⟨(D.R.Γ (D.g ψ₀) (F.obj z), z), src_Γ_obj ψ₀ hz⟩ := by
  rw [τ_eq ψ₀ hz, D.fibredMap_Linv]

/-- `s(τ_{ψ₀}(z)) = z`. -/
theorem src_τ (ψ₀ : MorY) {z : ObjY} (hz : F.obj z ∈ D.R.U) : Y.src (D.τ ψ₀ z) = z :=
  congrArg (fun p : MPolyfold.fibredProduct X.src F.obj => p.1.2) (fibredMap_τ ψ₀ hz)

/-- `F(τ_{ψ₀}(z)) = Γ(g, F(z))`. -/
theorem mor_τ (ψ₀ : MorY) {z : ObjY} (hz : F.obj z ∈ D.R.U) :
    F.mor (D.τ ψ₀ z) = D.R.Γ (D.g ψ₀) (F.obj z) :=
  congrArg (fun p : MPolyfold.fibredProduct X.src F.obj => p.1.1) (fibredMap_τ ψ₀ hz)

/-- `τ_{ψ₀}(z)` is the morphism `ψ` with `s(ψ) = z` and `F(ψ) = Γ(g, F(z))`. -/
theorem τ_eq_of {ψ₀ ψ : MorY} {z : ObjY} (hz : F.obj z ∈ D.R.U) (hs : Y.src ψ = z)
    (hm : F.mor ψ = D.R.Γ (D.g ψ₀) (F.obj z)) : D.τ ψ₀ z = ψ := by
  rw [τ_eq ψ₀ hz, ← D.Linv_fibredMap ψ]
  congr 1
  exact Subtype.ext (Prod.ext hm.symm hs.symm)

theorem continuousOn_τ (ψ₀ : MorY) : ContinuousOn (D.τ ψ₀) (F.obj ⁻¹' D.R.U) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hc : Continuous fun z : F.obj ⁻¹' D.R.U => D.R.Γ (D.g ψ₀) (F.obj z) :=
    (D.R.continuousOn_Γ _).comp_continuous ((continuous_obj F).comp continuous_subtype_val)
      fun z => z.2
  have hc' : Continuous fun z : F.obj ⁻¹' D.R.U =>
      (⟨(D.R.Γ (D.g ψ₀) (F.obj z), z), src_Γ_obj ψ₀ z.2⟩ :
        MPolyfold.fibredProduct X.src F.obj) :=
    (hc.prodMk continuous_subtype_val).subtype_mk _
  refine (D.continuous_Linv.comp hc').congr fun z => ?_
  simp only [domRestrict_apply, comp_apply]
  exact (τ_eq ψ₀ z.2).symm

theorem isScSmoothOn_τ (ψ₀ : MorY) : Y.PObj.IsScSmoothOn Y.PMor (D.τ ψ₀) (F.obj ⁻¹' D.R.U) :=
  isScSmoothOn_of_section Y (D.R.isOpen_U.preimage (continuous_obj F)) (continuousOn_τ ψ₀)
    fun _ hz => src_τ ψ₀ hz

/-- For `ψ₀` between points of `F⁻¹(x)`, `g(ψ₀) = F(ψ₀)` (Remark 8.2 (a)). -/
theorem val_g {ψ₀ : MorY} (hψ₀ : ψ₀ ∈ Y.morOn (F.obj ⁻¹' {x})) : (D.g ψ₀).val = F.mor ψ₀ := by
  have hm := F.remark_8_2_a hψ₀
  have hφ : F.mor ψ₀ ∈ X.morOn D.R.U :=
    ⟨by rw [hm.1]; exact D.R.mem_U, by rw [hm.2]; exact D.R.mem_U⟩
  have h := D.R.Γ_index hφ
  rw [hm.1, D.R.Γ_self] at h
  exact h

theorem connectedComponentIn_mor {ψ₀ : MorY} (hψ₀ : ψ₀ ∈ Y.morOn (F.obj ⁻¹' {x})) :
    connectedComponentIn (X.morOn D.R.U) (F.mor ψ₀) = D.R.Γ (D.g ψ₀) '' D.R.U := by
  rw [← val_g hψ₀]
  exact connectedComponentIn_morOn_val D.R _

theorem obj_src {ψ₀ : MorY} (hψ₀ : ψ₀ ∈ Y.morOn (F.obj ⁻¹' {x})) :
    F.obj (Y.src ψ₀) ∈ D.R.U := by
  rw [show F.obj (Y.src ψ₀) = x from hψ₀.1]
  exact D.R.mem_U

/-- `τ_{ψ₀}(s ψ₀) = ψ₀`. -/
theorem τ_self {ψ₀ : MorY} (hψ₀ : ψ₀ ∈ Y.morOn (F.obj ⁻¹' {x})) : D.τ ψ₀ (Y.src ψ₀) = ψ₀ :=
  τ_eq_of (obj_src hψ₀) rfl (by
    rw [show F.obj (Y.src ψ₀) = x from hψ₀.1, D.R.Γ_self, val_g hψ₀])

theorem obj_tgt_τ (ψ₀ : MorY) {z : ObjY} (hz : F.obj z ∈ D.R.U) :
    F.obj (Y.tgt (D.τ ψ₀ z)) = D.R.Φ (D.g ψ₀) (F.obj z) := by
  rw [← F.tgt_mor, mor_τ ψ₀ hz, D.R.tgt_Γ _ _ hz]

/-- **`t ∘ τ_{ψ₀}` maps `U(s ψ₀)` into `U(t ψ₀)`**: `U(s ψ₀)` is connected and `F⁻¹(U(x))` is the
disjoint union of the open `U(y)` (the counterpart of the claim, p. 278, that `ψ̂` maps `U(y)`
onto `U(y')`). -/
theorem tgt_τ_mem {ψ₀ : MorY} (hψ₀ : ψ₀ ∈ Y.morOn (F.obj ⁻¹' {x})) {z : ObjY}
    (hz : z ∈ D.U (Y.src ψ₀)) : Y.tgt (D.τ ψ₀ z) ∈ D.U (Y.tgt ψ₀) := by
  refine mapsTo_of_isPreconnected (f := Y.tgt ∘ D.τ ψ₀) (isConnected_U hψ₀.1).isPreconnected
    (Y.continuous_tgt.comp_continuousOn ((continuousOn_τ ψ₀).mono (U_subset _)))
    (fun y hy => isOpen_U hy) pairwiseDisjoint_U (fun w hw => ?_) (mem_U hψ₀.1) hψ₀.2 ?_ hz
  · rw [← preimage_eq]
    change F.obj (Y.tgt (D.τ ψ₀ w)) ∈ D.R.U
    rw [obj_tgt_τ ψ₀ (U_subset _ hw)]
    exact D.R.mapsTo_Φ _ (U_subset _ hw)
  · change Y.tgt (D.τ ψ₀ (Y.src ψ₀)) ∈ D.U (Y.tgt ψ₀)
    rw [τ_self hψ₀]
    exact mem_U hψ₀.2

/-- `t ∘ τ_{ψ₀} = (F|U(t ψ₀))⁻¹ ∘ Φ(g) ∘ F` on `U(s ψ₀)`. -/
theorem tgt_τ_eq {ψ₀ : MorY} (hψ₀ : ψ₀ ∈ Y.morOn (F.obj ⁻¹' {x})) {z : ObjY}
    (hz : z ∈ D.U (Y.src ψ₀)) :
    Y.tgt (D.τ ψ₀ z) = (D.σ (Y.tgt ψ₀) ∘ D.R.Φ (D.g ψ₀) ∘ F.obj) z := by
  have h := (isScDiffeoOn_U hψ₀.2).left_inv _ (tgt_τ_mem hψ₀ hz)
  rw [obj_tgt_τ ψ₀ (U_subset _ hz)] at h
  exact h.symm

/-- `(F|U(t ψ₀))⁻¹ ∘ Φ(g) ∘ F : U(s ψ₀) → U(t ψ₀)` is an sc-diffeomorphism. -/
theorem isScDiffeoOn_hat {ψ₀ : MorY} (hψ₀ : ψ₀ ∈ Y.morOn (F.obj ⁻¹' {x})) :
    Y.PObj.IsScDiffeoOn Y.PObj (D.σ (Y.tgt ψ₀) ∘ D.R.Φ (D.g ψ₀) ∘ F.obj)
      ((D.σ (Y.src ψ₀) ∘ D.R.Φ (D.g ψ₀)⁻¹) ∘ F.obj) (D.U (Y.src ψ₀)) (D.U (Y.tgt ψ₀)) :=
  (isScDiffeoOn_U hψ₀.2).symm.comp ((D.R.isScDiffeoOn_Φ _).comp (isScDiffeoOn_U hψ₀.1))

/-! #### The neighbourhoods `𝐔(ψ₀)` -/

/-- (3) `s : 𝐔(ψ₀) → U(s ψ₀)` is an sc-diffeomorphism, with inverse `τ_{ψ₀}`. -/
theorem isScDiffeoOn_src_sheet {ψ₀ : MorY} (hψ₀ : ψ₀ ∈ Y.morOn (F.obj ⁻¹' {x})) :
    Y.PMor.IsScDiffeoOn Y.PObj Y.src (D.τ ψ₀) (D.sheet ψ₀) (D.U (Y.src ψ₀)) :=
  EpGroupoid.NatRepFinite.isScDiffeoOn_src_image_of_section
    ((isScSmoothOn_τ ψ₀).mono (isOpen_U hψ₀.1) (U_subset _)) fun _ hz => src_τ ψ₀ (U_subset _ hz)

/-- (3) `t : 𝐔(ψ₀) → U(t ψ₀)` is an sc-diffeomorphism. -/
theorem isScDiffeoOn_tgt_sheet {ψ₀ : MorY} (hψ₀ : ψ₀ ∈ Y.morOn (F.obj ⁻¹' {x})) :
    Y.PMor.IsScDiffeoOn Y.PObj Y.tgt (D.τ ψ₀ ∘ ((D.σ (Y.src ψ₀) ∘ D.R.Φ (D.g ψ₀)⁻¹) ∘ F.obj))
      (D.sheet ψ₀) (D.U (Y.tgt ψ₀)) :=
  EpGroupoid.NatRepFinite.isScDiffeoOn_tgt_image_of_section
    ((isScSmoothOn_τ ψ₀).mono (isOpen_U hψ₀.1) (U_subset _))
    (fun _ hz => src_τ ψ₀ (U_subset _ hz)) (isScDiffeoOn_hat hψ₀) fun _ hz => tgt_τ_eq hψ₀ hz

theorem isOpen_sheet {ψ₀ : MorY} (hψ₀ : ψ₀ ∈ Y.morOn (F.obj ⁻¹' {x})) : IsOpen (D.sheet ψ₀) :=
  (isScDiffeoOn_src_sheet hψ₀).isOpen_source

theorem isConnected_sheet {ψ₀ : MorY} (hψ₀ : ψ₀ ∈ Y.morOn (F.obj ⁻¹' {x})) :
    IsConnected (D.sheet ψ₀) :=
  (isConnected_U hψ₀.1).image _ ((continuousOn_τ ψ₀).mono (U_subset _))

theorem mem_sheet {ψ₀ : MorY} (hψ₀ : ψ₀ ∈ Y.morOn (F.obj ⁻¹' {x})) : ψ₀ ∈ D.sheet ψ₀ :=
  ⟨Y.src ψ₀, mem_U hψ₀.1, τ_self hψ₀⟩

/-- The `𝐔(ψ₀)` are mutually disjoint: a common `ψ` has `s(ψ₀) = s(ψ₁)` (the `U(y)` are
disjoint) and `F(ψ₀) = F(ψ₁)` (the sheets of `𝐔(x)` are disjoint), so `L(ψ₀) = L(ψ₁)`. -/
theorem pairwiseDisjoint_sheet : (Y.morOn (F.obj ⁻¹' {x})).PairwiseDisjoint D.sheet := by
  intro ψ₀ hψ₀ ψ₁ hψ₁ hne
  refine disjoint_left.2 ?_
  rintro _ ⟨z, hz, rfl⟩ ⟨z', hz', he⟩
  have hzz : z' = z := by
    rw [← src_τ ψ₁ (U_subset _ hz'), he, src_τ ψ₀ (U_subset _ hz)]
  subst hzz
  have hs : Y.src ψ₁ = Y.src ψ₀ := pairwiseDisjoint_U.elim_set hψ₁.1 hψ₀.1 z' hz' hz
  have hFz := U_subset _ hz
  have hm := congrArg F.mor he
  rw [mor_τ ψ₀ hFz, mor_τ ψ₁ hFz] at hm
  have hg : D.g ψ₁ = D.g ψ₀ := (D.R.Γ_inj hFz).1 hm
  have hm' : F.mor ψ₁ = F.mor ψ₀ := by rw [← val_g hψ₀, ← val_g hψ₁, hg]
  refine hne ?_
  rw [← D.Linv_fibredMap ψ₀, ← D.Linv_fibredMap ψ₁]
  congr 1
  exact Subtype.ext (Prod.ext hm'.symm hs.symm)

/-- (2) **`𝐔(y, y')` is the union of the `𝐔(ψ₀)`, `ψ₀ : y → y'`**: for `ψ ∈ 𝐔(y, y')` with
`F(ψ) ∈ Γ(h, U(x))`, `ψ₀ = L⁻¹(h, y)` and `ψ = τ_{ψ₀}(s ψ)`. -/
theorem morOn_U_eq {y : ObjY} (hy : y ∈ F.obj ⁻¹' {x}) {y' : ObjY} (hy' : y' ∈ F.obj ⁻¹' {x}) :
    {ψ | Y.src ψ ∈ D.U y ∧ Y.tgt ψ ∈ D.U y'} = ⋃ ψ₀ ∈ Y.mor y y', D.sheet ψ₀ := by
  refine Subset.antisymm (fun ψ hψ => ?_) (iUnion₂_subset fun ψ₀ hψ₀ => ?_)
  · have hFz := U_subset _ hψ.1
    have hFt := U_subset _ hψ.2
    have hφ : F.mor ψ ∈ X.morOn D.R.U :=
      ⟨by rw [F.src_mor]; exact hFz, by rw [F.tgt_mor]; exact hFt⟩
    set h := D.R.index (F.mor ψ) with hh
    have hhx : X.src h.val = F.obj y := h.src_val.trans hy.symm
    set ψ₀ := D.Linv ⟨(h.val, y), hhx⟩
    have hL : F.fibredMap ψ₀ = ⟨(h.val, y), hhx⟩ := D.fibredMap_Linv _
    have hmψ₀ : F.mor ψ₀ = h.val :=
      congrArg (fun p : MPolyfold.fibredProduct X.src F.obj => p.1.1) hL
    have hsψ₀ : Y.src ψ₀ = y :=
      congrArg (fun p : MPolyfold.fibredProduct X.src F.obj => p.1.2) hL
    have htψ₀ : Y.tgt ψ₀ ∈ F.obj ⁻¹' {x} := by
      change F.obj (Y.tgt ψ₀) = x
      rw [← F.tgt_mor, hmψ₀]
      exact h.tgt_val
    have hψ₀m : ψ₀ ∈ Y.morOn (F.obj ⁻¹' {x}) := ⟨by rw [hsψ₀]; exact hy, htψ₀⟩
    have hg : D.g ψ₀ = h := by
      rw [g, hmψ₀, ← D.R.Γ_self h]
      exact D.R.index_Γ h D.R.mem_U
    have hτ : D.τ ψ₀ (Y.src ψ) = ψ := by
      refine τ_eq_of hFz rfl ?_
      rw [hg, hh, ← F.src_mor]
      exact (D.R.Γ_index hφ).symm
    have hzU : Y.src ψ ∈ D.U (Y.src ψ₀) := by rw [hsψ₀]; exact hψ.1
    have ht := tgt_τ_mem hψ₀m hzU
    rw [hτ] at ht
    have htt : Y.tgt ψ₀ = y' := pairwiseDisjoint_U.elim_set htψ₀ hy' _ ht hψ.2
    exact mem_iUnion₂.2 ⟨ψ₀, ⟨hsψ₀, htt⟩, Y.src ψ, hzU, hτ⟩
  · rintro _ ⟨z, hz, rfl⟩
    have hψ₀m : ψ₀ ∈ Y.morOn (F.obj ⁻¹' {x}) :=
      ⟨by rw [hψ₀.1]; exact hy, by rw [hψ₀.2]; exact hy'⟩
    refine ⟨by rw [src_τ ψ₀ (U_subset _ hz), ← hψ₀.1]; exact hz, ?_⟩
    rw [← hψ₀.2]
    exact tgt_τ_mem hψ₀m hz

/-- (4) **`F : 𝐔(ψ₀) → 𝐔(F(ψ₀)) = Γ(g, U(x))` is an sc-diffeomorphism**: on `𝐔(ψ₀)`,
`F = Γ(g, ·) ∘ F ∘ s = (s|𝐔(g))⁻¹ ∘ F ∘ s` (p. 279). -/
theorem isScDiffeoOn_mor_sheet {ψ₀ : MorY} (hψ₀ : ψ₀ ∈ Y.morOn (F.obj ⁻¹' {x})) :
    Y.PMor.IsScDiffeoOn X.PMor F.mor (D.τ ψ₀ ∘ (D.σ (Y.src ψ₀) ∘ X.src)) (D.sheet ψ₀)
      (D.R.Γ (D.g ψ₀) '' D.R.U) := by
  have hc := ((isScDiffeoOn_src_sheet hψ₀).symm.comp
    ((isScDiffeoOn_U hψ₀.1).symm.comp (D.R.isScDiffeoOn_src_image (D.g ψ₀)))).symm
  refine isScDiffeoOn_congr_left hc ?_
  rintro _ ⟨z, hz, rfl⟩
  simp only [comp_apply]
  rw [src_τ ψ₀ (U_subset _ hz), mor_τ ψ₀ (U_subset _ hz)]

/-- **The chart** built from the data. -/
def toChart : F.ProperCoveringChart x where
  R := D.R
  U := D.U
  sheet := D.sheet
  isOpen_U _ hy := isOpen_U hy
  isConnected_U _ hy := isConnected_U hy
  mem_U _ hy := mem_U hy
  pairwiseDisjoint_U := pairwiseDisjoint_U
  preimage_eq := preimage_eq
  isScDiffeoOn_obj _ hy := ⟨_, isScDiffeoOn_U hy⟩
  image_Γ := D.R.bijOn_Γ.image_eq
  iUnion_sheetX := by
    simp only [connectedComponentIn_morOn_val D.R]
    exact D.R.iUnion_image_Γ.symm
  pairwise_disjoint_sheetX g h hgh := by
    simp only [onFun, connectedComponentIn_morOn_val D.R]
    exact D.R.pairwise_disjoint_image_Γ hgh
  connectedComponentIn_eq := connectedComponentIn_morOn_val D.R
  isScDiffeoOn_src_sheetX g :=
    ⟨_, (connectedComponentIn_morOn_val D.R g).symm ▸ D.R.isScDiffeoOn_src_image g⟩
  isScDiffeoOn_tgt_sheetX g :=
    ⟨_, (connectedComponentIn_morOn_val D.R g).symm ▸ D.R.isScDiffeoOn_tgt_image g⟩
  isOpen_sheet _ hψ₀ := isOpen_sheet hψ₀
  isConnected_sheet _ hψ₀ := isConnected_sheet hψ₀
  mem_sheet _ hψ₀ := mem_sheet hψ₀
  pairwiseDisjoint_sheet := pairwiseDisjoint_sheet
  morOn_U_eq _ hy _ hy' := morOn_U_eq hy hy'
  isScDiffeoOn_src _ hψ₀ := ⟨_, isScDiffeoOn_src_sheet hψ₀⟩
  isScDiffeoOn_tgt _ hψ₀ := ⟨_, isScDiffeoOn_tgt_sheet hψ₀⟩
  isScDiffeoOn_mor _ hψ₀ :=
    ⟨_, (connectedComponentIn_mor hψ₀).symm ▸ isScDiffeoOn_mor_sheet hψ₀⟩
  comm_src _ _ ψ _ := (F.src_mor ψ).symm
  isScDiffeoOn_src_sheetF _ hψ₀ :=
    ⟨_, (connectedComponentIn_mor hψ₀).symm ▸ D.R.isScDiffeoOn_src_image (D.g _)⟩
  comm_tgt _ _ ψ _ := (F.tgt_mor ψ).symm
  isScDiffeoOn_tgt_sheetF _ hψ₀ :=
    ⟨_, (connectedComponentIn_mor hψ₀).symm ▸ D.R.isScDiffeoOn_tgt_image (D.g _)⟩

@[simp]
theorem toChart_R : D.toChart.R = D.R := rfl

end Data

end ProperCoveringLocal

/-! ### Theorem 8.5 -/

/-- **Theorem 8.5 (Proper Covering I)**, "for every sufficiently small `U(x)`": for a proper
covering functor `F : Y → X` and `x ∈ X` there is an open `W ∋ x` such that every natural
representation `(Φ, Γ)` of `G_x` on a connected open `U(x) ⊆ W` carries sets `U(y)`, `𝐔(ψ₀)` with
the properties (0)–(5) (`ProperCoveringChart`). -/
theorem theorem_8_5_of_naturalRep {F : EpFunctor Y X} (hF : F.IsProperCovering) (x : ObjX) :
    ∃ W : Set ObjX, IsOpen W ∧ x ∈ W ∧
      ∀ R : X.NaturalRep x, R.U ⊆ W → ∃ C : F.ProperCoveringChart x, C.R = R := by
  obtain ⟨W, hWo, hxW, hW⟩ := ProperCoveringLocal.exists_data hF x
  refine ⟨W, hWo, hxW, fun R hR => ?_⟩
  obtain ⟨D, rfl⟩ := hW R hR
  exact ⟨D.toChart, rfl⟩

/-- **Theorem 8.5 (Proper Covering I)**: for a proper covering functor `F : Y → X`, `x ∈ X` and
an open `V ∋ x` there are a natural representation `(Φ, Γ)` of `G_x` on a connected open
`U(x) ⊆ V` and sets `U(y)`, `y ∈ F⁻¹(x)`, and `𝐔(ψ₀)`, `ψ₀` a morphism between points of
`F⁻¹(x)`, with the properties (0)–(5) (the fields of `ProperCoveringChart`). -/
theorem theorem_8_5 {F : EpFunctor Y X} (hF : F.IsProperCovering) (x : ObjX) {V : Set ObjX}
    (hV : IsOpen V) (hx : x ∈ V) : ∃ C : F.ProperCoveringChart x, C.R.U ⊆ V := by
  obtain ⟨W, hWo, hxW, hW⟩ := theorem_8_5_of_naturalRep hF x
  obtain ⟨R, hR⟩ := X.theorem_7_1 x (hV.inter hWo) ⟨hx, hxW⟩
  obtain ⟨C, rfl⟩ := hW R fun z hz => (hR hz).2
  exact ⟨C, fun z hz => (hR hz).1⟩

/-! ### Remark 8.2 (b): the chart is determined by `U(x)` -/

namespace ProperCoveringChart

variable {F : EpFunctor Y X} {x : ObjX} (C : F.ProperCoveringChart x)

/-- `U(y)` is the connected component of `F⁻¹(U(x))` at `y`. -/
theorem connectedComponentIn_U {y : ObjY} (hy : y ∈ F.obj ⁻¹' {x}) :
    connectedComponentIn (F.obj ⁻¹' C.R.U) y = C.U y := by
  rw [C.preimage_eq]
  exact ProperCoveringLocal.connectedComponentIn_eq_of_iUnion C.isOpen_U C.isConnected_U
    C.pairwiseDisjoint_U hy (C.mem_U y hy)

/-- `𝐔(ψ₀)` is the connected component of `𝐔(s ψ₀, t ψ₀)` at `ψ₀`. -/
theorem connectedComponentIn_sheet {ψ₀ : MorY} (hψ₀ : ψ₀ ∈ Y.morOn (F.obj ⁻¹' {x})) :
    connectedComponentIn {ψ | Y.src ψ ∈ C.U (Y.src ψ₀) ∧ Y.tgt ψ ∈ C.U (Y.tgt ψ₀)} ψ₀ =
      C.sheet ψ₀ := by
  have hsub : Y.mor (Y.src ψ₀) (Y.tgt ψ₀) ⊆ Y.morOn (F.obj ⁻¹' {x}) := fun ψ hψ =>
    ⟨by rw [hψ.1]; exact hψ₀.1, by rw [hψ.2]; exact hψ₀.2⟩
  rw [C.morOn_U_eq _ hψ₀.1 _ hψ₀.2]
  exact ProperCoveringLocal.connectedComponentIn_eq_of_iUnion
    (fun ψ hψ => C.isOpen_sheet ψ (hsub hψ)) (fun ψ hψ => C.isConnected_sheet ψ (hsub hψ))
    (C.pairwiseDisjoint_sheet.subset hsub) ⟨rfl, rfl⟩ (C.mem_sheet ψ₀ hψ₀)

end ProperCoveringChart

/-- **Remark 8.2 (b)**: everything in Theorem 8.5 is determined by `U(x)`.  Two charts with the
same `U(x)` have the same `Φ` and `Γ` on `U(x)` (`Γ(g, ·)` is the continuous section of `s`
through `g`, `NaturalRep.Γ_eqOn`), the same `U(y)` and the same `𝐔(ψ₀)`. -/
theorem remark_8_2_b {F : EpFunctor Y X} {x : ObjX} (C C' : F.ProperCoveringChart x)
    (h : C.R.U = C'.R.U) :
    (∀ g, EqOn (C.R.Φ g) (C'.R.Φ g) C.R.U) ∧ (∀ g, EqOn (C.R.Γ g) (C'.R.Γ g) C.R.U) ∧
      (∀ y ∈ F.obj ⁻¹' {x}, C.U y = C'.U y) ∧
      ∀ ψ₀ ∈ Y.morOn (F.obj ⁻¹' {x}), C.sheet ψ₀ = C'.sheet ψ₀ := by
  have hcc : connectedComponentIn (C.R.U ∩ C'.R.U) x = C.R.U := by
    rw [← h, inter_self]
    exact C.R.isConnected_U.isPreconnected.connectedComponentIn C.R.mem_U
  have hU : ∀ y ∈ F.obj ⁻¹' {x}, C.U y = C'.U y := fun y hy => by
    rw [← C.connectedComponentIn_U hy, ← C'.connectedComponentIn_U hy, h]
  refine ⟨fun g => hcc ▸ C.R.Φ_eqOn C'.R g, fun g => hcc ▸ C.R.Γ_eqOn C'.R g, hU,
    fun ψ₀ hψ₀ => ?_⟩
  rw [← C.connectedComponentIn_sheet hψ₀, ← C'.connectedComponentIn_sheet hψ₀,
    hU _ hψ₀.1, hU _ hψ₀.2]

end EpFunctor

end Polyfold
