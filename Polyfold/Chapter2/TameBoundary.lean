import Polyfold.Chapter2.TameFaces
import Polyfold.Chapter2.Metrizable
import Mathlib.CategoryTheory.Category.Preorder

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §2.5,
**Definitions 2.5.18, 2.5.19** (pp. 62–63), and Appendix §2.7.4 "Formalism Associated to a
Boundary with Corners", **Proposition 2.7.5** (p. 78), **Definition 2.7.6** (p. 79),
**Proposition 2.7.7**, **Definition 2.7.8** (p. 80), **Definitions 2.7.9, 2.7.10** (p. 81),
**Definition 2.7.11** (p. 82).  All of these are new in the 2021 edition (the 2017 text and the
2014 preprint, which the rest of Chapter 2 follows, have no §2.7.4).  The topology on `bX`
(Lemma 2.7.15, Propositions 2.7.12, 2.7.16, Theorem 2.7.13, Definition 2.7.14) is in
`Polyfold/Chapter2/TameBoundaryTopology.lean`.

# Tame sub-M-polyfolds and the boundary structure functor

## The text, paraphrased

(Definition 2.5.18) The structure induced on a sub-M-polyfold `Y ⊆ X` is called tame if it has an
equivalent atlas with tame local models.  (Definition 2.5.19) For a tame `X`, the sub-M-polyfold
`Y` is a tame sub-M-polyfold if every `y ∈ Y` has an open `V` and an sc-smooth retraction
`r : V → V` with (1) `r(V) = Y ∩ V`, (2) `d_X ∘ r = d_X` on `V`, (3) at smooth `y ∈ Y ∩ V` an
sc-subspace `A` of the reduced tangent space `T_y^R X` with `T_yX = T_yY ⊕ A`.  (An example
follows: in `[0,∞)² × ℝ` the set `{(x, y, 0)}` is a tame sub-M-polyfold, the diagonal ray
`{(x, x, 0)}` is not, although its induced structure is tame.)

(Proposition 2.7.5) In a tame `X` every `x` has an open `V` on which `d_X ≤ d_X(x)`, such that
every `y ∈ V` lies in exactly `d_X(y)` faces of `V`, and with an open `U(x) ⊆ V` such that a face
of `V` meeting `U(x)` contains `x`.  (Definition 2.7.6) An open `V` is face-structured if every
`y ∈ V` lies in exactly `d_X(y)` faces of `V`; `N_X^{all}` is the set of these, `N_X` the
nonempty ones with `d_X|V` bounded, `N_{X,x}` those `V ∈ N_X` containing `x` with
`d_X ≤ d_X(x)` on `V`; then `N_X = ⋃_x N_{X,x}`.  (Proposition 2.7.7) `N_{X,x} ≠ ∅`; nonempty
open subsets of members of `N_X` and nonempty intersections are in `N_X`; `N_{X,x}` is closed
under intersections.  (Definition 2.7.8) The category `L_X` has objects `(x, V)`, `x ∈ ∂X`,
`V ∈ N_{X,x}`, and one morphism `(x, V) → (y, W)` iff `V ⊆ W`, `x` lies in `d_X(x)` faces of `W`
and all of them contain `y`; composition is proved by matching the faces through `x`, `y`, `z`.
(Definition 2.7.9) `F_X(x, V)` is the set of faces of `V` through `x`, and a morphism sends `θ`
to the unique face `θ'` of `W` through `x` and `y` with `θ ∩ θ'` open in `θ` ((2.42), (2.43)).
(Definition 2.7.10) An admissible triple `(x, V, θ)` has `x ∈ ∂X`, `V ∈ N_{X,x}`,
`θ ∈ F_X(x, V)`; two are equivalent if `x = x'` and some `(x, V'') ∈ L_X`, `V'' ⊆ V ∩ V'`, has a
face `θ''` sent to `θ` and `θ'`; `bX` is the set of classes and `B[x, V, θ] = x`.
(Definition 2.7.11) `U(x, V, θ)` is the set of classes `[y, V', θ']` with `y ∈ θ`, a morphism
`(y, V') → (x, V)` sending `θ'` to `θ`, and `Φ_{(x,V,θ)} : U(x, V, θ) → θ` is `[y, V', θ'] ↦ y`,
a bijection by (2.44).

## What is formalized

* The abstract layer (`namespace TameBoundary`), for any `d : X → ℕ` on a topological space:
  `faceAt`, `IsFaceIn` (faces of an open `V`), `facesThrough` (`F_X(y, V)`), `faceExt` (the map
  `θ ↦ θ'` of (2.43), with its characterization `faceExt_unique`), and the **corner axioms**
  `IsCornerIndex d` (upper semicontinuity plus separated `LocalPieces` of `{d = 1}`).  All of
  §2.7.4 is proved from `IsCornerIndex`, so that it applies verbatim to other spaces with a
  degeneracy index (the object spaces of tame ep-groupoids, 2021 §7.6.5).
* `MPolyfold.isCornerIndex_degIndex`: the degeneracy index of a tame M-polyfold satisfies the
  corner axioms (`exists_localPieces_chart`, from Lemma 4.C `local_face_structure` and
  `subset_coordHyper_of_isPreconnected` of `TameFaces.lean`).
* **Proposition 2.7.5**: `TameBoundary.proposition_2_7_5`, `MPolyfold.proposition_2_7_5_2021`;
  (3) for every open `V ∋ x`: `exists_nbhd_faces_mem`.
* **Definition 2.7.6**: `IsFaceStructuredOpen`, `faceStructuredOpens`, `faceStructuredNbhds`,
  `faceStructuredNbhdsAt`, and the remark `faceStructuredNbhds_eq_iUnion`.
* **Proposition 2.7.7**: `MPolyfold.proposition_2_7_7_2021` (from `faceStructuredNbhdsAt_nonempty`,
  `sUnion_faceStructuredNbhds`, `mem_faceStructuredNbhds_of_subset`,
  `inter_mem_faceStructuredNbhds`, `inter_mem_faceStructuredNbhdsAt`).
* **Definition 2.7.8**: `IsMor`, its composition law `IsMor.trans`, the objects `LObj`, the thin
  category (`Preorder (LObj hd)` and Mathlib's `Preorder.smallCategory`);
  `MPolyfold.LocalBoundaryCategory`.
* **Definition 2.7.9**: `boundaryFunctor : LObj hd ⥤ Type u` (`MPolyfold.boundaryStructureFunctor`),
  with `F_X(φ)` injective (`boundaryFunctor_map_injective`) and bijective for morphisms
  `(x, V) → (x, W)` (`boundaryFunctor_map_bijective`).
* **Definition 2.7.10**: `BTriple` (admissible triples), `BRel` (an equivalence relation:
  `BRel.refl`, `BRel.symm`, `BRel.trans`), `BSpace` (`bX`, `MPolyfold.TameBoundarySpace`), `bMap`
  (`B`, `MPolyfold.tameBoundaryMap`), with `range_bMap` (the image is `∂X`) and
  `encard_bMap_preimage` (`x` has exactly `d(x)` preimages).
* **Definition 2.7.11**: `uSet` (`U(x, V, θ)`), `phi` (`Φ_{(x,V,θ)}`), `phi_injective`,
  `bMap_image_uSet`, and `phi_bijective_of_isCenteredAt`.
* **Definitions 2.5.18, 2.5.19**: `MPolyfold.HasTameInducedStructure`, `MPolyfold.TameSubData`,
  `MPolyfold.IsTameSubMPolyfold` (condition (3) in a chart: `HasReducedComplementAt`).
* Witnesses: `isCornerIndex_zero` (`d ≡ 0`); `MPolyfold.quadrantPolyfold n W` (the tame
  quadrant `[0,∞)ⁿ ⊕ W`, `quadrantPolyfold_isTame`), whose corner has `n` preimages in `bX`
  (`quadrantPolyfold_encard_preimage`, `quadrantPolyfold_tameBoundarySpace_nonempty`);
  `hasTameInducedStructure_univ`, `isTameSubMPolyfold_univ`, `quadrantPolyfold_univ` (`Y = X`).

## What the text leaves implicit, and the choices made

* **(2.44) does not hold as we read it** for every `V ∈ N_{X,x}`: `Φ_{(x,V,θ)}` is injective,
  but its image is `θ ∩ V^x`, where `V^x = {y ∈ V | every face of V through y contains x}`
  (`bMap_image_uSet`).  A point `y ∈ θ` lying on a face of `V` that misses `x` admits no morphism
  `(y, V') → (x, V)`; this happens e.g. in `[0,∞)³` for `x = (0,0,1)` and `V` a thin convex
  neighbourhood of the segment from `x` to `(0,1,0)` (proved in
  `Polyfold/Chapter2/TameBoundaryExample.lean`, `phi_not_surjective_2021`).  The map is a
  bijection onto `θ` when every
  face of `V` contains `x` (`IsCenteredAt`, `phi_bijective_of_isCenteredAt`), and `V^x` is such a
  neighbourhood in `N_{X,x}` (`isCenteredAt_reach`, `reach_mem_faceStructuredNbhdsAt`), which is
  what the text's "taking `V` sufficiently small" provides.
* The faces of an open `V` are those of `V` with the induced M-polyfold structure; as its
  degeneracy index is `d_X|V` (2021 Proposition 2.4.4), they are defined directly from `d_X`
  (`faceAt d V p` is the closure in `V` of the component of `V ∩ {d = 1}` through `p`).
* `F_X(φ)(θ)` is defined as the union of the faces of `W` containing `θ` (`faceExt`); it is the
  unique face of `W` through `x` and `y` with `θ ∩ θ'` open in `θ` (`faceExt_unique`).
* `L_X` is encoded as a preorder (at most one morphism); the functor goes to `Type u`.
* In Definition 2.7.11, membership in `U(x, V, θ)` is read as "for some representative".
* Definition 2.5.19 (3) is stated in a chart (gap G.7: `T_yX` has no linear structure here),
  for some chart around `y`; it is literally Chapter 4's `IsGeneralPositionRetractAt` condition.
  Its independence of the chart, the text's remark that a tame sub-M-polyfold is tame, and the
  example in `[0,∞)² × ℝ` are not formalized.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

namespace TameBoundary

universe u

variable {X : Type u} [TopologicalSpace X]

/-! ### Faces of open subsets -/

section Faces

variable (d : X → ℕ)

/-- The face of the open set `V` through a point `p ∈ V` with `d(p) = 1`: the closure in `V` of
the connected component through `p` of `{y ∈ V | d(y) = 1}`. -/
def faceAt (V : Set X) (p : X) : Set X :=
  V ∩ closure (connectedComponentIn (V ∩ {y | d y = 1}) p)

/-- `θ` is a **face of the open set `V`** (2021 Definition 2.5.10 for `V`): the closure in `V` of
a connected component of `{y ∈ V | d(y) = 1}`. -/
def IsFaceIn (V θ : Set X) : Prop := ∃ p ∈ V, d p = 1 ∧ θ = faceAt d V p

/-- The faces of `V` containing `y` (the set `F_X(y, V)` of 2021 Definition 2.7.9). -/
def facesThrough (V : Set X) (y : X) : Set (Set X) := {θ | IsFaceIn d V θ ∧ y ∈ θ}

/-- **Local pieces** of the stratum `{d = 1}` at `y`, inside `N`: an open `B ∋ y`, `B ⊆ N`, and
`d(y)` preconnected sets `ℓ_i ⊆ N ∩ {d = 1}` accumulating at `y` which cover `B ∩ {d = 1}`.  In a
tame chart these are the sets `r({z ∈ C | |z − φ(y)| < ε, I(z) = {i}})`, `i ∈ I(φ(y))`. -/
structure LocalPieces (y : X) (N : Set X) where
  /-- The open neighbourhood `B` of `y`. -/
  B : Set X
  isOpen_B : IsOpen B
  mem_B : y ∈ B
  B_subset : B ⊆ N
  /-- The pieces `ℓ_i`, `i < d(y)`. -/
  piece : Fin (d y) → Set X
  isPreconnected : ∀ i, IsPreconnected (piece i)
  piece_subset : ∀ i, piece i ⊆ N ∩ {z | d z = 1}
  mem_closure : ∀ i, y ∈ closure (piece i)
  cover : B ∩ {z | d z = 1} ⊆ ⋃ i, piece i

/-- **The corner axioms** for `d : X → ℕ`: `d` is upper semicontinuous (2021 Lemma 2.4.3, preprint
Lemma 2.23) and every `x` has an open neighbourhood `D` such that every `y ∈ D` has local pieces
of `{d = 1}` in arbitrarily small neighbourhoods, which are separated in `D`: no preconnected
subset of `D ∩ {d = 1}` meets two of them.  The degeneracy index of a tame M-polyfold satisfies
them (`MPolyfold.isCornerIndex_degIndex`). -/
structure IsCornerIndex : Prop where
  eventually_le : ∀ x, ∀ᶠ y in 𝓝 x, d y ≤ d x
  exists_pieces : ∀ x, ∃ D, IsOpen D ∧ x ∈ D ∧ ∀ y ∈ D, ∀ N ∈ 𝓝 y,
    ∃ L : LocalPieces d y N, ∀ S ⊆ D ∩ {z | d z = 1}, IsPreconnected S →
      ∀ i j, (S ∩ L.piece i).Nonempty → (S ∩ L.piece j).Nonempty → i = j

variable {d}

namespace LocalPieces

variable {y : X} {N : Set X} (L : LocalPieces d y N)

lemma nonempty_piece (i : Fin (d y)) : (L.piece i).Nonempty :=
  closure_nonempty_iff.1 ⟨y, L.mem_closure i⟩

/-- A point of the piece `ℓ_i`. -/
def pt (i : Fin (d y)) : X := (L.nonempty_piece i).some

lemma pt_mem (i : Fin (d y)) : L.pt i ∈ L.piece i := (L.nonempty_piece i).some_mem

/-- Local pieces inside `N` are local pieces inside every `N' ⊇ N`. -/
def mono {N' : Set X} (h : N ⊆ N') : LocalPieces d y N' where
  B := L.B
  isOpen_B := L.isOpen_B
  mem_B := L.mem_B
  B_subset := L.B_subset.trans h
  piece := L.piece
  isPreconnected := L.isPreconnected
  piece_subset i := (L.piece_subset i).trans (inter_subset_inter_left _ h)
  mem_closure := L.mem_closure
  cover := L.cover

@[simp] lemma mono_piece {N' : Set X} (h : N ⊆ N') : (L.mono h).piece = L.piece := rfl
@[simp] lemma mono_pt {N' : Set X} (h : N ⊆ N') : (L.mono h).pt = L.pt := rfl
@[simp] lemma mono_B {N' : Set X} (h : N ⊆ N') : (L.mono h).B = L.B := rfl

end LocalPieces

variable (hd : IsCornerIndex d)
include hd

lemma IsCornerIndex.exists_localPieces {y : X} {N : Set X} (hN : N ∈ 𝓝 y) :
    Nonempty (LocalPieces d y N) := by
  obtain ⟨D, hD, hyD, h⟩ := hd.exists_pieces y
  obtain ⟨L, -⟩ := h y hyD N hN
  exact ⟨L⟩

omit hd

lemma faceAt_subset (V : Set X) (p : X) : faceAt d V p ⊆ V := inter_subset_left

lemma connectedComponentIn_subset_faceAt {V : Set X} (p : X) :
    connectedComponentIn (V ∩ {y | d y = 1}) p ⊆ faceAt d V p := fun _ hz =>
  ⟨(connectedComponentIn_subset _ _ hz).1, subset_closure hz⟩

lemma mem_faceAt_self {V : Set X} {p : X} (hp : p ∈ V) (h1 : d p = 1) : p ∈ faceAt d V p :=
  connectedComponentIn_subset_faceAt p (mem_connectedComponentIn ⟨hp, h1⟩)

lemma isFaceIn_faceAt {V : Set X} {p : X} (hp : p ∈ V) (h1 : d p = 1) :
    IsFaceIn d V (faceAt d V p) := ⟨p, hp, h1, rfl⟩

lemma IsFaceIn.subset {V θ : Set X} (h : IsFaceIn d V θ) : θ ⊆ V := by
  obtain ⟨p, -, -, rfl⟩ := h; exact faceAt_subset V p

/-- A local piece meeting a component of `{d = 1} ∩ V` lies in it. -/
lemma LocalPieces.piece_subset_cc {y : X} {V : Set X} (L : LocalPieces d y V) {i : Fin (d y)}
    {p : X} (h : (L.piece i ∩ connectedComponentIn (V ∩ {z | d z = 1}) p).Nonempty) :
    L.piece i ⊆ connectedComponentIn (V ∩ {z | d z = 1}) p := by
  obtain ⟨g, hgi, hgp⟩ := h
  rw [connectedComponentIn_eq hgp]
  exact (L.isPreconnected i).subset_connectedComponentIn hgi (L.piece_subset i)

/-- If `y` lies in the closure of a component `G` of `V ∩ {d = 1}`, then `G` contains one of the
local pieces at `y`. -/
lemma LocalPieces.exists_piece_subset {y : X} {V : Set X} (L : LocalPieces d y V) {p : X}
    (hy : y ∈ closure (connectedComponentIn (V ∩ {z | d z = 1}) p)) :
    ∃ i, L.piece i ⊆ connectedComponentIn (V ∩ {z | d z = 1}) p := by
  obtain ⟨g, hgB, hgG⟩ := mem_closure_iff.1 hy L.B L.isOpen_B L.mem_B
  have hg1 : d g = 1 := (connectedComponentIn_subset _ _ hgG).2
  obtain ⟨i, hgi⟩ := mem_iUnion.1 (L.cover ⟨hgB, hg1⟩)
  exact ⟨i, L.piece_subset_cc ⟨g, hgi, hgG⟩⟩

/-- The same statement for a point `y'` of the neighbourhood `B` of the pieces at `y`. -/
lemma LocalPieces.exists_piece_subset_of_mem_B {y y' : X} {V : Set X} (L : LocalPieces d y V)
    (hy' : y' ∈ L.B) {p : X} (h : y' ∈ closure (connectedComponentIn (V ∩ {z | d z = 1}) p)) :
    ∃ i, L.piece i ⊆ connectedComponentIn (V ∩ {z | d z = 1}) p := by
  obtain ⟨g, hgB, hgG⟩ := mem_closure_iff.1 h L.B L.isOpen_B hy'
  have hg1 : d g = 1 := (connectedComponentIn_subset _ _ hgG).2
  obtain ⟨i, hgi⟩ := mem_iUnion.1 (L.cover ⟨hgB, hg1⟩)
  exact ⟨i, L.piece_subset_cc ⟨g, hgi, hgG⟩⟩

include hd

/-- **The interior of a face**: the points of `faceAt V p` with `d = 1` form the component
`G` through `p` (for a face `F = closure(G)`, `F ∩ {d = 1} = G`). -/
theorem faceAt_inter_eq {V : Set X} (hV : IsOpen V) {p : X} :
    faceAt d V p ∩ {y | d y = 1} = connectedComponentIn (V ∩ {y | d y = 1}) p := by
  refine Subset.antisymm ?_ fun z hz =>
    ⟨connectedComponentIn_subset_faceAt p hz, (connectedComponentIn_subset _ _ hz).2⟩
  rintro q ⟨⟨hqV, hqcl⟩, hq1⟩
  obtain ⟨L⟩ := hd.exists_localPieces (hV.mem_nhds hqV)
  obtain ⟨i, hi⟩ := L.exists_piece_subset hqcl
  obtain ⟨j, hqj⟩ := mem_iUnion.1 (L.cover ⟨L.mem_B, hq1⟩)
  have hij : j = i := by
    have h1 := i.isLt; have h2 := j.isLt
    simp only [mem_ofPred_eq] at hq1
    ext; omega
  rw [hij] at hqj
  exact hi hqj

theorem mem_cc_of_mem_faceAt {V : Set X} (hV : IsOpen V) {p q : X} (hq : q ∈ faceAt d V p)
    (h1 : d q = 1) : q ∈ connectedComponentIn (V ∩ {y | d y = 1}) p := by
  rw [← faceAt_inter_eq hd hV]; exact ⟨hq, h1⟩

/-- A face through a point `q` with `d(q) = 1` is the face of `q`. -/
theorem IsFaceIn.eq_faceAt_of_mem {V θ : Set X} (hV : IsOpen V) (hθ : IsFaceIn d V θ) {q : X}
    (hq : q ∈ θ) (h1 : d q = 1) : θ = faceAt d V q := by
  obtain ⟨p, -, -, rfl⟩ := hθ
  unfold faceAt
  rw [connectedComponentIn_eq (mem_cc_of_mem_faceAt hd hV hq h1)]

theorem faceAt_eq_faceAt_iff {V : Set X} (hV : IsOpen V) {p q : X} (hq : q ∈ V) (h1 : d q = 1) :
    faceAt d V p = faceAt d V q ↔ q ∈ connectedComponentIn (V ∩ {y | d y = 1}) p := by
  constructor
  · intro h
    exact mem_cc_of_mem_faceAt hd hV (h ▸ mem_faceAt_self hq h1) h1
  · intro h
    unfold faceAt
    rw [connectedComponentIn_eq h]

omit hd

/-- Every point of `V` is in the face through each local piece at `y` (for pieces inside `V`). -/
lemma LocalPieces.mem_faceAt_pt {y : X} {V : Set X} (L : LocalPieces d y V) (hy : y ∈ V)
    (i : Fin (d y)) : y ∈ faceAt d V (L.pt i) := by
  refine ⟨hy, closure_mono ?_ (L.mem_closure i)⟩
  exact (L.isPreconnected i).subset_connectedComponentIn (L.pt_mem i) (L.piece_subset i)

lemma LocalPieces.isFaceIn_faceAt_pt {y : X} {V : Set X} (L : LocalPieces d y V) (i : Fin (d y)) :
    IsFaceIn d V (faceAt d V (L.pt i)) :=
  isFaceIn_faceAt ((L.piece_subset i (L.pt_mem i)).1) (L.piece_subset i (L.pt_mem i)).2

include hd

/-- The faces of `V` through `y` are the faces through the local pieces at `y`. -/
theorem LocalPieces.facesThrough_eq {y : X} {V : Set X} (hV : IsOpen V) (hy : y ∈ V)
    (L : LocalPieces d y V) :
    facesThrough d V y = range fun i => faceAt d V (L.pt i) := by
  ext θ
  constructor
  · rintro ⟨⟨p, hpV, hp1, rfl⟩, hyθ⟩
    obtain ⟨i, hi⟩ := L.exists_piece_subset hyθ.2
    refine ⟨i, ?_⟩
    have hpt := hi (L.pt_mem i)
    exact ((faceAt_eq_faceAt_iff hd hV (L.piece_subset i (L.pt_mem i)).1
      (L.piece_subset i (L.pt_mem i)).2).2 hpt).symm
  · rintro ⟨i, rfl⟩
    exact ⟨L.isFaceIn_faceAt_pt i, L.mem_faceAt_pt hy i⟩

omit hd in
lemma encard_range_le_fin {α : Type*} {n : ℕ} (f : Fin n → α) : (range f).encard ≤ n := by
  classical
  have : range f = ((Finset.univ.image f : Finset α) : Set α) := by simp
  rw [this, Set.encard_coe_eq_coe_finsetCard]
  exact_mod_cast (Finset.card_image_le).trans (by simp)

omit hd in
lemma injective_of_encard_range_eq {α : Type*} {n : ℕ} (f : Fin n → α)
    (h : (range f).encard = n) : Injective f := by
  classical
  have hr : range f = ((Finset.univ.image f : Finset α) : Set α) := by simp
  rw [hr, Set.encard_coe_eq_coe_finsetCard] at h
  have h' : (Finset.univ.image f).card = (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin]; exact_mod_cast h
  have := Finset.card_image_iff.1 h'
  exact fun a b hab => this (Finset.mem_coe.2 (Finset.mem_univ a))
    (Finset.mem_coe.2 (Finset.mem_univ b)) hab

omit hd in
lemma encard_range_of_injective_fin {α : Type*} {n : ℕ} {f : Fin n → α} (hf : Injective f) :
    (range f).encard = n := by
  rw [← image_univ, hf.encard_image, encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin]

/-- A point `y` of the open `V` lies in at most `d(y)` faces of `V` (2021 Proposition 2.5.14,
last statement, for `V`). -/
theorem encard_facesThrough_le {V : Set X} (hV : IsOpen V) {y : X} (hy : y ∈ V) :
    (facesThrough d V y).encard ≤ d y := by
  obtain ⟨L⟩ := hd.exists_localPieces (hV.mem_nhds hy)
  rw [L.facesThrough_eq hd hV hy]
  exact encard_range_le_fin _

/-- `V` is face-structured at `y` iff the faces through the local pieces at `y` are distinct. -/
theorem LocalPieces.encard_facesThrough_eq_iff {y : X} {V : Set X} (hV : IsOpen V) (hy : y ∈ V)
    (L : LocalPieces d y V) :
    (facesThrough d V y).encard = d y ↔ Injective fun i => faceAt d V (L.pt i) := by
  rw [L.facesThrough_eq hd hV hy]
  exact ⟨injective_of_encard_range_eq _, encard_range_of_injective_fin⟩

/-- Faces lie in the boundary `{d ≥ 1}`. -/
theorem one_le_of_mem_isFaceIn {V θ : Set X} (hV : IsOpen V) (hθ : IsFaceIn d V θ) {y : X}
    (hy : y ∈ θ) : 1 ≤ d y := by
  by_contra h0
  have hθV := hθ.subset hy
  obtain ⟨L⟩ := hd.exists_localPieces (hV.mem_nhds hθV)
  have hfa : (facesThrough d V y).encard ≤ d y := encard_facesThrough_le hd hV hθV
  have : d y = 0 := by omega
  rw [this] at hfa
  have : facesThrough d V y = ∅ := encard_eq_zero.1 (nonpos_iff_eq_zero.1 hfa)
  exact (this ▸ (⟨hθ, hy⟩ : θ ∈ facesThrough d V y) : θ ∈ (∅ : Set (Set X)))

omit hd in
/-- The faces through a point `y'` near `y` pass through `y`: for local pieces `L` at `y` in `V`,
every face of `V` through a point of `L.B` passes through `y`. -/
theorem LocalPieces.facesThrough_subset {y y' : X} {V : Set X} (hy : y ∈ V)
    (L : LocalPieces d y V) (hy' : y' ∈ L.B) : facesThrough d V y' ⊆ facesThrough d V y := by
  rintro θ ⟨⟨p, hpV, hp1, rfl⟩, hy'θ⟩
  obtain ⟨i, hi⟩ := L.exists_piece_subset_of_mem_B hy' hy'θ.2
  exact ⟨⟨p, hpV, hp1, rfl⟩, hy, closure_mono hi (L.mem_closure i)⟩

end Faces

/-! ### Extension of faces to larger open sets -/

section Ext

variable (d : X → ℕ)

/-- The face of `V` containing the face `θ` of an open `U ⊆ V` (the map `F_X(φ)` of (2.43)): the
union of the faces of `V` containing `θ` (there is exactly one, `faceExt_faceAt`). -/
def faceExt (V θ : Set X) : Set X := ⋃₀ {θ' | IsFaceIn d V θ' ∧ θ ⊆ θ'}

variable {d} (hd : IsCornerIndex d)
include hd

omit hd in
lemma faceAt_subset_faceAt {U V : Set X} (hUV : U ⊆ V) (p : X) : faceAt d U p ⊆ faceAt d V p :=
  inter_subset_inter hUV
    (closure_mono (connectedComponentIn_mono p (inter_subset_inter_left _ hUV)))

theorem faceExt_faceAt {U V : Set X} (hV : IsOpen V) (hUV : U ⊆ V) {p : X} (hp : p ∈ U)
    (h1 : d p = 1) : faceExt d V (faceAt d U p) = faceAt d V p := by
  have : {θ' | IsFaceIn d V θ' ∧ faceAt d U p ⊆ θ'} = {faceAt d V p} := by
    ext θ'
    simp only [mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨hθ', hsub'⟩
      exact hθ'.eq_faceAt_of_mem hd hV (hsub' (mem_faceAt_self hp h1)) h1
    · rintro rfl
      exact ⟨isFaceIn_faceAt (hUV hp) h1, faceAt_subset_faceAt hUV p⟩
  rw [faceExt, this, sUnion_singleton]

/-- `faceExt V θ` is a face of `V` containing `θ`. -/
theorem IsFaceIn.faceExt {U V θ : Set X} (hV : IsOpen V) (hUV : U ⊆ V) (hθ : IsFaceIn d U θ) :
    IsFaceIn d V (faceExt d V θ) ∧ θ ⊆ faceExt d V θ := by
  obtain ⟨p, hp, h1, rfl⟩ := hθ
  rw [faceExt_faceAt hd hV hUV hp h1]
  exact ⟨isFaceIn_faceAt (hUV hp) h1, faceAt_subset_faceAt hUV p⟩

theorem faceExt_self {V θ : Set X} (hV : IsOpen V) (hθ : IsFaceIn d V θ) : faceExt d V θ = θ := by
  obtain ⟨p, hp, h1, rfl⟩ := hθ
  exact faceExt_faceAt hd hV subset_rfl hp h1

/-- Functoriality of the extension: `U ⊆ V ⊆ W`. -/
theorem faceExt_faceExt {U V W θ : Set X} (hV : IsOpen V) (hW : IsOpen W) (hUV : U ⊆ V)
    (hVW : V ⊆ W) (hθ : IsFaceIn d U θ) : faceExt d W (faceExt d V θ) = faceExt d W θ := by
  obtain ⟨p, hp, h1, rfl⟩ := hθ
  rw [faceExt_faceAt hd hV hUV hp h1, faceExt_faceAt hd hW (hUV.trans hVW) hp h1,
    faceExt_faceAt hd hW hVW (hUV hp) h1]

theorem faceExt_mem_facesThrough {U V θ : Set X} (hV : IsOpen V) (hUV : U ⊆ V) {y : X}
    (hθ : θ ∈ facesThrough d U y) : faceExt d V θ ∈ facesThrough d V y :=
  ⟨(hθ.1.faceExt hd hV hUV).1, (hθ.1.faceExt hd hV hUV).2 hθ.2⟩

/-- **The text's description of `F_X(φ)`** ((2.43)): `faceExt V θ` is the unique face `θ'` of `V`
such that `θ ∩ θ'` is a nonempty open subset of `θ`. -/
theorem faceExt_unique {U V θ θ' : Set X} (hV : IsOpen V) (hUV : U ⊆ V) (hθ : IsFaceIn d U θ)
    (hθ' : IsFaceIn d V θ') (hne : (θ ∩ θ').Nonempty) (hopen : ∃ N, IsOpen N ∧ θ ∩ θ' = θ ∩ N) :
    θ' = faceExt d V θ := by
  obtain ⟨p, hp, h1, rfl⟩ := hθ
  obtain ⟨N, hN, hNe⟩ := hopen
  obtain ⟨z, hz⟩ := hne
  rw [hNe] at hz
  obtain ⟨g, hgN, hgG⟩ := mem_closure_iff.1 hz.1.2 N hN hz.2
  have hg := connectedComponentIn_subset _ _ hgG
  have hgθ : g ∈ faceAt d U p ∩ θ' := by
    rw [hNe]; exact ⟨connectedComponentIn_subset_faceAt p hgG, hgN⟩
  rw [hθ'.eq_faceAt_of_mem hd hV hgθ.2 hg.2, faceExt_faceAt hd hV hUV hp h1]
  exact (faceAt_eq_faceAt_iff hd hV (hUV hg.1) hg.2).2
    (connectedComponentIn_mono p (inter_subset_inter_left _ hUV) hgG) |>.symm

/-- Every face of `V` through `y ∈ U` extends a face of `U` through `y` (`F_X` is onto for
morphisms `(y, U) → (y, V)`). -/
theorem exists_faceExt_eq {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ⊆ V) {y : X}
    (hy : y ∈ U) {θ' : Set X} (hθ' : θ' ∈ facesThrough d V y) :
    ∃ θ ∈ facesThrough d U y, faceExt d V θ = θ' := by
  obtain ⟨L⟩ := hd.exists_localPieces (hU.mem_nhds hy)
  obtain ⟨⟨p, hpV, hp1, rfl⟩, hyθ'⟩ := hθ'
  obtain ⟨i, hi⟩ := (L.mono hUV).exists_piece_subset hyθ'.2
  refine ⟨faceAt d U (L.pt i), ⟨L.isFaceIn_faceAt_pt i, L.mem_faceAt_pt hy i⟩, ?_⟩
  have hpt := L.piece_subset i (L.pt_mem i)
  rw [faceExt_faceAt hd hV hUV hpt.1 hpt.2]
  exact ((faceAt_eq_faceAt_iff hd hV (hUV hpt.1) hpt.2).2 (hi (L.pt_mem i))).symm

/-- `F_X` is injective on the faces through `y` when `V` is face-structured at `y`. -/
theorem faceExt_injOn {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ⊆ V) {y : X}
    (hy : y ∈ U) (hVy : (facesThrough d V y).encard = d y) :
    InjOn (faceExt d V) (facesThrough d U y) := by
  obtain ⟨L⟩ := hd.exists_localPieces (hU.mem_nhds hy)
  have hinj := ((L.mono hUV).encard_facesThrough_eq_iff hd hV (hUV hy)).1 hVy
  rw [L.facesThrough_eq hd hU hy]
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
  have hpi := L.piece_subset i (L.pt_mem i)
  have hpj := L.piece_subset j (L.pt_mem j)
  simp only at hij
  rw [faceExt_faceAt hd hV hUV hpi.1 hpi.2, faceExt_faceAt hd hV hUV hpj.1 hpj.2] at hij
  have : i = j := hinj hij
  rw [this]

end Ext

/-! ### Face-structured open sets (Definition 2.7.6) and Proposition 2.7.5 -/

section FaceStructured

variable (d : X → ℕ)

/-- **2021 Definition 2.7.6 (1)**: the open set `V` is **face-structured** if every `y ∈ V` lies in
exactly `d(y)` faces of `V`. -/
def IsFaceStructuredOpen (V : Set X) : Prop :=
  IsOpen V ∧ ∀ y ∈ V, (facesThrough d V y).encard = d y

/-- **2021 Definition 2.7.6 (2)**: `N_X^{all}`, the face-structured open subsets. -/
def faceStructuredOpens : Set (Set X) := {V | IsFaceStructuredOpen d V}

/-- **2021 Definition 2.7.6 (3)**: `N_X`, the nonempty face-structured open subsets on which `d` is
bounded. -/
def faceStructuredNbhds : Set (Set X) :=
  {V | V ∈ faceStructuredOpens d ∧ V.Nonempty ∧ BddAbove (d '' V)}

/-- **2021 Definition 2.7.6 (4)**: `N_{X,x}`, the `V ∈ N_X` containing `x` with `d ≤ d(x)` on
`V`. -/
def faceStructuredNbhdsAt (x : X) : Set (Set X) :=
  {V | V ∈ faceStructuredNbhds d ∧ x ∈ V ∧ ∀ y ∈ V, d y ≤ d x}

/-- The remark after 2021 Definition 2.7.6: `N_X = ⋃_x N_{X,x}` (a `V ∈ N_X` contains a point
where `d|V` is maximal). -/
theorem faceStructuredNbhds_eq_iUnion :
    faceStructuredNbhds d = ⋃ x, faceStructuredNbhdsAt d x := by
  ext V
  simp only [mem_iUnion]
  constructor
  · intro hV
    have hne := hV.2.1
    have hbdd := hV.2.2
    obtain ⟨x, hxV, hx⟩ := Nat.sSup_mem (hne.image d) hbdd
    exact ⟨x, hV, hxV, fun y hy => hx ▸ le_csSup hbdd (mem_image_of_mem d hy)⟩
  · rintro ⟨x, hV, -⟩; exact hV

variable {d} (hd : IsCornerIndex d)
include hd

/-- An open subset of a face-structured open set is face-structured. -/
theorem IsFaceStructuredOpen.mono {U V : Set X} (hV : IsFaceStructuredOpen d V) (hU : IsOpen U)
    (hUV : U ⊆ V) : IsFaceStructuredOpen d U := by
  refine ⟨hU, fun y hy => ?_⟩
  obtain ⟨L⟩ := hd.exists_localPieces (hU.mem_nhds hy)
  rw [L.encard_facesThrough_eq_iff hd hU hy]
  have hinj := ((L.mono hUV).encard_facesThrough_eq_iff hd hV.1 (hUV hy)).1 (hV.2 y (hUV hy))
  intro i j hij
  apply hinj
  simp only at hij ⊢
  have hpj := L.piece_subset j (L.pt_mem j)
  have := (faceAt_eq_faceAt_iff hd hU hpj.1 hpj.2).1 hij
  exact (faceAt_eq_faceAt_iff hd hV.1 (hUV hpj.1) hpj.2).2
    (connectedComponentIn_mono _ (inter_subset_inter_left _ hUV) this)

/-- Every point has an open neighbourhood `D` all of whose open subsets are face-structured. -/
theorem exists_nbhd_forall_isFaceStructuredOpen (x : X) :
    ∃ D, IsOpen D ∧ x ∈ D ∧ ∀ V, IsOpen V → V ⊆ D → IsFaceStructuredOpen d V := by
  obtain ⟨D, hD, hxD, h⟩ := hd.exists_pieces x
  refine ⟨D, hD, hxD, fun V hV hVD => ⟨hV, fun y hy => ?_⟩⟩
  obtain ⟨L, hsep⟩ := h y (hVD hy) V (hV.mem_nhds hy)
  rw [L.encard_facesThrough_eq_iff hd hV hy]
  intro i j hij
  have hpi := L.piece_subset i (L.pt_mem i)
  have hpj := L.piece_subset j (L.pt_mem j)
  have hj := (faceAt_eq_faceAt_iff hd hV hpj.1 hpj.2).1 hij
  exact hsep (connectedComponentIn (V ∩ {z | d z = 1}) (L.pt i))
    ((connectedComponentIn_subset _ _).trans (inter_subset_inter_left _ hVD))
    isPreconnected_connectedComponentIn i j
    ⟨L.pt i, mem_connectedComponentIn hpi, L.pt_mem i⟩ ⟨L.pt j, hj, L.pt_mem j⟩

/-- **2021 Proposition 2.7.5 (3)**, for every open `V ∋ x`: there is an open `U(x) ⊆ V` such that
every face of `V` containing a point of `U(x)` contains `x`. -/
theorem exists_nbhd_faces_mem {V : Set X} (hV : IsOpen V) {x : X} (hx : x ∈ V) :
    ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ V ∧ ∀ θ, IsFaceIn d V θ → ∀ y ∈ U, y ∈ θ → x ∈ θ := by
  obtain ⟨L⟩ := hd.exists_localPieces (hV.mem_nhds hx)
  exact ⟨L.B, L.isOpen_B, L.mem_B, L.B_subset, fun θ hθ y hy hyθ =>
    (L.facesThrough_subset hx hy ⟨hθ, hyθ⟩).2⟩

/-- **2021 Proposition 2.7.5** (abstract form): every `x` has an open neighbourhood `V` with
(1) `d(y) ≤ d(x)` on `V`; (2) every `y ∈ V` lies in exactly `d(y)` faces of `V`; (3) an open
`U(x) ⊆ V` such that every face of `V` containing a point of `U(x)` contains `x`. -/
theorem proposition_2_7_5 (x : X) :
    ∃ V, IsOpen V ∧ x ∈ V ∧ (∀ y ∈ V, d y ≤ d x) ∧
      (∀ y ∈ V, (facesThrough d V y).encard = d y) ∧
      ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ V ∧ ∀ θ, IsFaceIn d V θ → ∀ y ∈ U, y ∈ θ → x ∈ θ := by
  obtain ⟨D, hD, hxD, hfs⟩ := exists_nbhd_forall_isFaceStructuredOpen hd x
  obtain ⟨t, ht, hto, hxt⟩ := mem_nhds_iff.1 (hd.eventually_le x)
  have hV : IsOpen (D ∩ t) := hD.inter hto
  have hxV : x ∈ D ∩ t := ⟨hxD, hxt⟩
  exact ⟨D ∩ t, hV, hxV, fun y hy => ht hy.2, (hfs _ hV inter_subset_left).2,
    exists_nbhd_faces_mem hd hV hxV⟩

/-- **2021 Proposition 2.7.7 (1)**: `N_{X,x}` is nonempty. -/
theorem faceStructuredNbhdsAt_nonempty (x : X) : (faceStructuredNbhdsAt d x).Nonempty := by
  obtain ⟨V, hV, hxV, hle, hfs, -⟩ := proposition_2_7_5 hd x
  exact ⟨V, ⟨⟨hV, hfs⟩, ⟨x, hxV⟩, ⟨d x, by rintro _ ⟨y, hy, rfl⟩; exact hle y hy⟩⟩, hxV, hle⟩

/-- **2021 Proposition 2.7.7 (1)**: `N_X` is an open covering of `X`. -/
theorem sUnion_faceStructuredNbhds : ⋃₀ faceStructuredNbhds d = univ := by
  refine eq_univ_of_forall fun x => ?_
  obtain ⟨V, hV⟩ := faceStructuredNbhdsAt_nonempty hd x
  exact ⟨V, hV.1, hV.2.1⟩

/-- **2021 Proposition 2.7.7 (2)**: a nonempty open subset of a `V ∈ N_X` belongs to `N_X`. -/
theorem mem_faceStructuredNbhds_of_subset {U V : Set X} (hV : V ∈ faceStructuredNbhds d)
    (hU : IsOpen U) (hUne : U.Nonempty) (hUV : U ⊆ V) : U ∈ faceStructuredNbhds d :=
  ⟨IsFaceStructuredOpen.mono hd hV.1 hU hUV, hUne, hV.2.2.mono (image_mono hUV)⟩

/-- **2021 Proposition 2.7.7 (3)**: `N_X` is closed under nonempty intersections. -/
theorem inter_mem_faceStructuredNbhds {V V' : Set X} (hV : V ∈ faceStructuredNbhds d)
    (hV' : V' ∈ faceStructuredNbhds d) (hne : (V ∩ V').Nonempty) :
    V ∩ V' ∈ faceStructuredNbhds d :=
  mem_faceStructuredNbhds_of_subset hd hV (hV.1.1.inter hV'.1.1) hne inter_subset_left

/-- An open `U` with `x ∈ U ⊆ V`, `V ∈ N_{X,x}`, belongs to `N_{X,x}`. -/
theorem mem_faceStructuredNbhdsAt_of_subset {x : X} {U V : Set X}
    (hV : V ∈ faceStructuredNbhdsAt d x) (hU : IsOpen U) (hxU : x ∈ U) (hUV : U ⊆ V) :
    U ∈ faceStructuredNbhdsAt d x :=
  ⟨mem_faceStructuredNbhds_of_subset hd hV.1 hU ⟨x, hxU⟩ hUV, hxU, fun y hy => hV.2.2 y (hUV hy)⟩

/-- **2021 Proposition 2.7.7 (3)**: `N_{X,x}` is closed under intersections. -/
theorem inter_mem_faceStructuredNbhdsAt {x : X} {V V' : Set X}
    (hV : V ∈ faceStructuredNbhdsAt d x) (hV' : V' ∈ faceStructuredNbhdsAt d x) :
    V ∩ V' ∈ faceStructuredNbhdsAt d x :=
  mem_faceStructuredNbhdsAt_of_subset hd hV (hV.1.1.1.inter hV'.1.1.1) ⟨hV.2.1, hV'.2.1⟩
    inter_subset_left

omit hd in
lemma IsFaceStructuredOpen.isOpen {V : Set X} (h : IsFaceStructuredOpen d V) : IsOpen V := h.1

omit hd in
lemma mem_faceStructuredNbhdsAt.isOpen {x : X} {V : Set X} (h : V ∈ faceStructuredNbhdsAt d x) :
    IsOpen V := h.1.1.1

omit hd in
lemma mem_faceStructuredNbhdsAt.encard {x : X} {V : Set X} (h : V ∈ faceStructuredNbhdsAt d x)
    {y : X} (hy : y ∈ V) : (facesThrough d V y).encard = d y := h.1.1.2 y hy

end FaceStructured

/-! ### The local boundary structure category `L_X` (Definition 2.7.8) and the functor `F_X`
(Definition 2.7.9) -/

section Category

variable (d : X → ℕ)

/-- The morphism condition of **2021 Definition 2.7.8**: `mor((x, V), (y, W))` is nonempty iff
`V ⊆ W`, `x` lies in `d(x)` faces of `W`, and each of them contains `y`. -/
def IsMor (x : X) (V : Set X) (y : X) (W : Set X) : Prop :=
  V ⊆ W ∧ (facesThrough d W x).encard = d x ∧ ∀ θ ∈ facesThrough d W x, y ∈ θ

variable {d}

theorem isMor_refl {x : X} {V : Set X} (hV : V ∈ faceStructuredNbhdsAt d x) : IsMor d x V x V :=
  ⟨subset_rfl, hV.1.1.2 x hV.2.1, fun _ hθ => hθ.2⟩

/-- `(x, V) → (x, W)` for `V ⊆ W`. -/
theorem isMor_of_subset {x : X} {V W : Set X} (hVW : V ⊆ W) (hW : W ∈ faceStructuredNbhdsAt d x) :
    IsMor d x V x W :=
  ⟨hVW, hW.1.1.2 x hW.2.1, fun _ hθ => hθ.2⟩

variable (hd : IsCornerIndex d)
include hd

/-- **The composition law of 2021 Definition 2.7.8** (the text's argument after the definition):
`(x, V) → (y, W) → (z, Q)` gives `(x, V) → (z, Q)`.  Every face `γ` of `Q` through `x` extends a
face `θ` of `W` through `x` (`exists_faceExt_eq`), which contains `y`; so `y ∈ γ` and then
`z ∈ γ`. -/
theorem IsMor.trans {x y z : X} {V W Q : Set X} (hx : x ∈ V) (hW : IsOpen W)
    (hQ : IsFaceStructuredOpen d Q) (h1 : IsMor d x V y W) (h2 : IsMor d y W z Q) :
    IsMor d x V z Q := by
  refine ⟨h1.1.trans h2.1, hQ.2 x (h2.1 (h1.1 hx)), fun γ hγ => ?_⟩
  obtain ⟨θ, hθ, hθγ⟩ := exists_faceExt_eq hd hW hQ.1 h2.1 (h1.1 hx) hγ
  have hsub := (hθ.1.faceExt hd hQ.1 h2.1).2
  rw [hθγ] at hsub
  exact h2.2.2 γ ⟨hγ.1, hsub (h1.2.2 θ hθ)⟩

omit hd in
/-- An object `(x, V)` of the **local boundary structure category `L_X`** (2021 Definition 2.7.8):
`x ∈ ∂X` and `V ∈ N_{X,x}`. -/
@[ext]
structure LObj (hd : IsCornerIndex d) where
  /-- The point `x ∈ ∂X`. -/
  x : X
  /-- The face-structured neighbourhood `V ∈ N_{X,x}`. -/
  V : Set X
  mem : V ∈ faceStructuredNbhdsAt d x
  one_le : 1 ≤ d x

/-- **2021 Definition 2.7.8**: `L_X` is a thin category (`#mor ≤ 1`): the preorder `a ≤ b` iff
`mor(a, b) ≠ ∅`; Mathlib's `CategoryTheory.Preorder.smallCategory` turns it into the category
with `Hom a b = ULift (PLift (a ≤ b))`.  Reflexivity is the identity, transitivity the
composition law (`IsMor.trans`). -/
instance : Preorder (LObj hd) where
  le a b := IsMor d a.x a.V b.x b.V
  le_refl a := isMor_refl a.mem
  le_trans a b c h1 h2 := IsMor.trans hd a.mem.2.1 b.mem.1.1.1 c.mem.1.1 h1 h2

lemma LObj.le_iff {a b : LObj hd} : a ≤ b ↔ IsMor d a.x a.V b.x b.V := Iff.rfl

omit hd in
/-- `F_X(x, V)`: the faces of `V` containing `x` (`d(x) = #F_X(x, V)`). -/
lemma LObj.encard_facesThrough {hd' : IsCornerIndex d} (a : LObj hd') :
    (facesThrough d a.V a.x).encard = d a.x :=
  a.mem.1.1.2 a.x a.mem.2.1

/-- The image of a face under a morphism lies in `F_X(y, W)`. -/
theorem faceExt_mem_of_isMor {x y : X} {V W θ : Set X} (hW : IsOpen W) (h : IsMor d x V y W)
    (hθ : θ ∈ facesThrough d V x) : faceExt d W θ ∈ facesThrough d W y := by
  have h' := faceExt_mem_facesThrough hd hW h.1 hθ
  exact ⟨h'.1, h.2.2 _ h'⟩

open CategoryTheory in
/-- **2021 Definition 2.7.9**: the **boundary structure functor** `F_X : L_X → SET`,
`F_X(x, V) = {θ ∈ Face(V) | x ∈ θ}`, and for a morphism `(x, V) → (y, W)` the map
`θ ↦ θ'`, `θ'` the face of `W` containing `θ` (`faceExt`; the text's "the face `θ'` of `W`
through `x` and `y` with `θ ∩ θ'` open in `θ`", `faceExt_unique`). -/
def boundaryFunctor : LObj hd ⥤ Type u where
  obj a := facesThrough d a.V a.x
  map {_ b} f := TypeCat.ofHom fun θ =>
    ⟨faceExt d b.V θ.1, faceExt_mem_of_isMor hd b.mem.1.1.1 (leOfHom f) θ.2⟩
  map_id a := ConcreteCategory.hom_ext _ _ fun θ =>
    Subtype.ext (faceExt_self hd a.mem.1.1.1 θ.2.1)
  map_comp {_ b c} f g := ConcreteCategory.hom_ext _ _ fun θ =>
    Subtype.ext (faceExt_faceExt hd b.mem.1.1.1 c.mem.1.1.1 (leOfHom f).1 (leOfHom g).1
      θ.2.1).symm

open CategoryTheory in
@[simp] lemma boundaryFunctor_map_val {a b : LObj hd} (f : a ⟶ b)
    (θ : (boundaryFunctor hd).obj a) : ((boundaryFunctor hd).map f θ).1 = faceExt d b.V θ.1 := rfl

open CategoryTheory in
/-- `F_X(φ)` is injective (the text's "we obtain the injection" (2.43)). -/
theorem boundaryFunctor_map_injective {a b : LObj hd} (f : a ⟶ b) :
    Injective ((boundaryFunctor hd).map f) := by
  have hab := leOfHom f
  intro θ₁ θ₂ h
  have h' := congrArg Subtype.val h
  simp only [boundaryFunctor_map_val] at h'
  -- both images are faces of `W` through `x`; pull back to faces of `W` through `x`
  have hx : a.x ∈ b.V := hab.1 a.mem.2.1
  have hinj := faceExt_injOn hd a.mem.1.1.1 b.mem.1.1.1 hab.1 a.mem.2.1 hab.2.1
  exact Subtype.ext (hinj θ₁.2 θ₂.2 h')

open CategoryTheory in
/-- For a morphism `(x, V) → (x, W)` (same point), `F_X(φ)` is a bijection. -/
theorem boundaryFunctor_map_bijective {a b : LObj hd} (f : a ⟶ b) (hx : a.x = b.x) :
    Bijective ((boundaryFunctor hd).map f) := by
  refine ⟨boundaryFunctor_map_injective hd f, fun θ' => ?_⟩
  have hab := leOfHom f
  have hθ' : θ'.1 ∈ facesThrough d b.V a.x := by rw [hx]; exact θ'.2
  obtain ⟨θ, hθ, hθe⟩ := exists_faceExt_eq hd a.mem.1.1.1 b.mem.1.1.1 hab.1 a.mem.2.1 hθ'
  exact ⟨⟨θ, hθ⟩, Subtype.ext hθe⟩

end Category

/-! ### The set `bX` of admissible boundary triples (Definition 2.7.10) -/

section Triples

variable {d : X → ℕ} (hd : IsCornerIndex d)

/-- An **admissible boundary triple** `(x, V, θ)` (2021 Definition 2.7.10): `x ∈ ∂X`,
`V ∈ N_{X,x}` and `θ ∈ F_X(x, V)`. -/
structure BTriple extends LObj hd where
  /-- The face `θ ∈ F_X(x, V)`. -/
  θ : Set X
  mem_faces : θ ∈ facesThrough d V x

/-- **2021 Definition 2.7.10**: `(x, V, θ) ∼ (x', V', θ')` iff `x = x'` and there is
`V'' ∈ N_{X,x}`, `V'' ⊆ V ∩ V'`, and `θ'' ∈ F_X(x, V'')` with `F_X(φ)(θ'') = θ`,
`F_X(φ')(θ'') = θ'` for the morphisms `φ : (x, V'') → (x, V)`, `φ' : (x, V'') → (x, V')`
(`F_X(φ) = faceExt V`, `boundaryFunctor_map_val`). -/
def BRel (s t : BTriple hd) : Prop :=
  s.x = t.x ∧ ∃ V'' ∈ faceStructuredNbhdsAt d s.x, V'' ⊆ s.V ∩ t.V ∧
    ∃ θ'' ∈ facesThrough d V'' s.x, faceExt d s.V θ'' = s.θ ∧ faceExt d t.V θ'' = t.θ

include hd in
/-- Given `V' ∈ N_{X,x}` inside `V` and a face `θ` of `V` through `x`, the face `θ'` of `V'`
through `x` with `faceExt V θ' = θ`. -/
theorem exists_face_restrict {x : X} {V V' θ : Set X} (hV : V ∈ faceStructuredNbhdsAt d x)
    (hV' : IsOpen V') (hxV' : x ∈ V') (hV'V : V' ⊆ V) (hθ : θ ∈ facesThrough d V x) :
    ∃ θ' ∈ facesThrough d V' x, faceExt d V θ' = θ :=
  exists_faceExt_eq hd hV' hV.1.1.1 hV'V hxV' hθ

theorem BRel.refl (s : BTriple hd) : BRel hd s s :=
  ⟨rfl, s.V, s.mem, by simp, s.θ, s.mem_faces, faceExt_self hd s.mem.1.1.1 s.mem_faces.1,
    faceExt_self hd s.mem.1.1.1 s.mem_faces.1⟩

theorem BRel.symm {s t : BTriple hd} (h : BRel hd s t) : BRel hd t s := by
  obtain ⟨hx, V'', hV'', hsub, θ'', hθ'', h1, h2⟩ := h
  refine ⟨hx.symm, V'', hx ▸ hV'', fun z hz => ⟨(hsub hz).2, (hsub hz).1⟩, θ'', hx ▸ hθ'', h2, h1⟩

/-- The common refinement in `BRel`: a face of a smaller `V*` which extends to both. -/
theorem BRel.trans {s t r : BTriple hd} (h₁ : BRel hd s t) (h₂ : BRel hd t r) : BRel hd s r := by
  obtain ⟨hst, V₁, hV₁, hV₁sub, θ₁, hθ₁, e₁s, e₁t⟩ := h₁
  obtain ⟨htr, V₂, hV₂, hV₂sub, θ₂, hθ₂, e₂t, e₂r⟩ := h₂
  rw [← hst] at hV₂ hθ₂
  have hV := inter_mem_faceStructuredNbhdsAt hd hV₁ hV₂
  obtain ⟨θ, hθ, hθe⟩ := exists_face_restrict hd hV₁ hV.1.1.1 hV.2.1 inter_subset_left hθ₁
  have hV₁s : V₁ ⊆ s.V := fun z hz => (hV₁sub hz).1
  have hV₁t : V₁ ⊆ t.V := fun z hz => (hV₁sub hz).2
  have hV₂t : V₂ ⊆ t.V := fun z hz => (hV₂sub hz).1
  have hV₂r : V₂ ⊆ r.V := fun z hz => (hV₂sub hz).2
  -- `θ** = faceExt V₂ θ = θ₂`
  have h22 : faceExt d V₂ θ = θ₂ := by
    have hmem := faceExt_mem_facesThrough hd hV₂.1.1.1 inter_subset_right hθ
    refine faceExt_injOn hd hV₂.1.1.1 t.mem.1.1.1 hV₂t hV₂.2.1 (hst ▸ t.encard_facesThrough) hmem
      hθ₂ ?_
    rw [faceExt_faceExt hd hV₂.1.1.1 t.mem.1.1.1 inter_subset_right hV₂t hθ.1, e₂t,
      ← faceExt_faceExt hd hV₁.1.1.1 t.mem.1.1.1 inter_subset_left hV₁t hθ.1, hθe, e₁t]
  refine ⟨hst.trans htr, V₁ ∩ V₂, hV, fun z hz => ⟨hV₁s hz.1, hV₂r hz.2⟩, θ, hθ, ?_, ?_⟩
  · rw [← faceExt_faceExt hd hV₁.1.1.1 s.mem.1.1.1 inter_subset_left hV₁s hθ.1, hθe, e₁s]
  · rw [← faceExt_faceExt hd hV₂.1.1.1 r.mem.1.1.1 inter_subset_right hV₂r hθ.1, h22, e₂r]

/-- The setoid of 2021 Definition 2.7.10. -/
def bSetoid : Setoid (BTriple hd) where
  r := BRel hd
  iseqv := ⟨BRel.refl hd, BRel.symm hd, BRel.trans hd⟩

/-- **2021 Definition 2.7.10**: the set `bX` of equivalence classes `[x, V, θ]` of admissible
boundary triples. -/
def BSpace : Type u := Quotient (bSetoid hd)

/-- The class `[x, V, θ]`. -/
def BTriple.cls (t : BTriple hd) : BSpace hd := Quotient.mk (bSetoid hd) t

lemma BTriple.cls_eq_cls {s t : BTriple hd} : s.cls = t.cls ↔ BRel hd s t := Quotient.eq

lemma BSpace.exists_rep (p : BSpace hd) : ∃ t : BTriple hd, t.cls = p := Quotient.exists_rep p

/-- **2021 Definition 2.7.10**: the natural map `B : bX → X`, `B([x, V, θ]) = x`. -/
def bMap : BSpace hd → X := Quotient.lift (fun t : BTriple hd => t.x) fun _ _ h => h.1

@[simp] lemma bMap_cls (t : BTriple hd) : bMap hd t.cls = t.x := rfl

end Triples

/-! ### The sets `U(x, V, θ)` and the maps `Φ_{(x,V,θ)}` (Definition 2.7.11) -/

section USet

variable (d : X → ℕ)

/-- `V^x`: the points of `V` all of whose faces in `V` contain `x`.  For `y ∈ V` there is a
morphism `(y, V') → (x, V)` iff `y ∈ V^x` (and `V' ⊆ V`). -/
def reach (V : Set X) (x : X) : Set X := {y | y ∈ V ∧ ∀ γ ∈ facesThrough d V y, x ∈ γ}

/-- `V` is **centred at `x`** if every face of `V` contains `x`. -/
def IsCenteredAt (x : X) (V : Set X) : Prop := ∀ θ, IsFaceIn d V θ → x ∈ θ

variable {d} (hd : IsCornerIndex d)

/-- **2021 Definition 2.7.11**: `U(x, V, θ)` is the set of classes `[y, V', θ']` (with some
representative) such that (1) `y ∈ θ`, (2) `mor((y, V'), (x, V)) ≠ ∅`, (3) `F_X(φ)(θ') = θ` for
`φ : (y, V') → (x, V)`. -/
def uSet (t : BTriple hd) : Set (BSpace hd) :=
  {p | ∃ s : BTriple hd, s.cls = p ∧ s.x ∈ t.θ ∧ IsMor d s.x s.V t.x t.V ∧ faceExt d t.V s.θ = t.θ}

lemma bMap_mem_of_mem_uSet {t : BTriple hd} {p : BSpace hd} (hp : p ∈ uSet hd t) :
    bMap hd p ∈ t.θ := by
  obtain ⟨s, rfl, h1, -⟩ := hp; exact h1

/-- **2021 Definition 2.7.11, (2.44)**: the map `Φ_{(x,V,θ)} : U(x, V, θ) → θ`,
`[y, V', θ'] ↦ y`, the restriction of `B`. -/
def phi (t : BTriple hd) : uSet hd t → t.θ := fun p => ⟨bMap hd p.1, bMap_mem_of_mem_uSet hd p.2⟩

@[simp] lemma phi_coe (t : BTriple hd) (p : uSet hd t) : (phi hd t p : X) = bMap hd p.1 := rfl

include hd

theorem cls_mem_uSet (t : BTriple hd) : t.cls ∈ uSet hd t :=
  ⟨t, rfl, t.mem_faces.2, isMor_refl t.mem, faceExt_self hd t.mem.1.1.1 t.mem_faces.1⟩

/-- If `(y, V', θ') → (x, V, θ)` (a morphism with `F_X(φ)(θ') = θ`), then
`U(y, V', θ') ⊆ U(x, V, θ)`. -/
theorem uSet_subset {s t : BTriple hd} (h : IsMor d s.x s.V t.x t.V)
    (he : faceExt d t.V s.θ = t.θ) : uSet hd s ⊆ uSet hd t := by
  rintro p ⟨r, rfl, -, hr2, hr3⟩
  have hrt : IsMor d r.x r.V t.x t.V := IsMor.trans hd r.mem.2.1 s.mem.1.1.1 t.mem.1.1 hr2 h
  have hext : faceExt d t.V r.θ = t.θ := by
    rw [← he, ← hr3, faceExt_faceExt hd s.mem.1.1.1 t.mem.1.1.1 hr2.1 h.1 r.mem_faces.1]
  refine ⟨r, rfl, ?_, hrt, hext⟩
  rw [← hext]
  exact (r.mem_faces.1.faceExt hd t.mem.1.1.1 hrt.1).2 r.mem_faces.2

/-- `Φ_{(x,V,θ)}` is injective: two classes in `U(x, V, θ)` over the same point agree. -/
theorem bMap_injOn_uSet (t : BTriple hd) : InjOn (bMap hd) (uSet hd t) := by
  rintro _ ⟨s, rfl, -, hs, hse⟩ _ ⟨s', rfl, -, hs', hse'⟩ hxx
  simp only [bMap_cls] at hxx
  rw [BTriple.cls_eq_cls]
  have hs'V : s'.V ∈ faceStructuredNbhdsAt d s.x := by rw [hxx]; exact s'.mem
  have hV := inter_mem_faceStructuredNbhdsAt hd s.mem hs'V
  obtain ⟨θ, hθ, hθe⟩ :=
    exists_faceExt_eq hd hV.1.1.1 s.mem.1.1.1 inter_subset_left hV.2.1 s.mem_faces
  refine ⟨hxx, s.V ∩ s'.V, hV, subset_rfl, θ, hθ, hθe, ?_⟩
  have hmem := faceExt_mem_facesThrough hd s'.mem.1.1.1 inter_subset_right hθ
  have hs'θ : s'.θ ∈ facesThrough d s'.V s.x := by rw [hxx]; exact s'.mem_faces
  refine faceExt_injOn hd s'.mem.1.1.1 t.mem.1.1.1 hs'.1 hs'V.2.1
    (t.mem.1.1.2 _ (hs.1 s.mem.2.1)) hmem hs'θ ?_
  rw [faceExt_faceExt hd s'.mem.1.1.1 t.mem.1.1.1 inter_subset_right hs'.1 hθ.1,
    ← faceExt_faceExt hd s.mem.1.1.1 t.mem.1.1.1 inter_subset_left hs.1 hθ.1, hθe, hse, hse']

theorem phi_injective (t : BTriple hd) : Injective (phi hd t) := fun p q h =>
  Subtype.ext (bMap_injOn_uSet hd t p.2 q.2 (congrArg Subtype.val h))

omit hd in
lemma reach_subset (V : Set X) (x : X) : reach d V x ⊆ V := fun _ h => h.1

omit hd in
lemma mem_reach_self {V : Set X} {x : X} (hx : x ∈ V) : x ∈ reach d V x :=
  ⟨hx, fun _ hγ => hγ.2⟩

/-- `V^x` is open. -/
theorem isOpen_reach {V : Set X} (hV : IsOpen V) (x : X) : IsOpen (reach d V x) := by
  rw [isOpen_iff_forall_mem_open]
  intro y hy
  obtain ⟨L⟩ := hd.exists_localPieces (hV.mem_nhds hy.1)
  exact ⟨L.B, fun y' hy' =>
    ⟨L.B_subset hy', fun γ hγ => hy.2 γ (L.facesThrough_subset hy.1 hy' hγ)⟩,
    L.isOpen_B, L.mem_B⟩

/-- **The image of `Φ_{(x,V,θ)}`** is `θ ∩ V^x`, an open subset of `θ` containing `x`.  (The text
calls `Φ_{(x,V,θ)} : U(x, V, θ) → θ` a bijection; this holds as we read it when `V` is centred at
`x`, `bMap_image_uSet_of_isCenteredAt`, e.g. for `V^x`, but not for every `V ∈ N_{X,x}`.) -/
theorem bMap_image_uSet (t : BTriple hd) : bMap hd '' uSet hd t = t.θ ∩ reach d t.V t.x := by
  ext y
  constructor
  · rintro ⟨_, ⟨s, rfl, hs1, hs2, -⟩, rfl⟩
    exact ⟨hs1, t.mem_faces.1.subset hs1, hs2.2.2⟩
  · rintro ⟨hyθ, hyV, hyx⟩
    have hy1 : 1 ≤ d y := one_le_of_mem_isFaceIn hd t.mem.1.1.1 t.mem_faces.1 hyθ
    obtain ⟨W, hW⟩ := faceStructuredNbhdsAt_nonempty hd y
    have hV' := mem_faceStructuredNbhdsAt_of_subset hd hW (hW.1.1.1.inter t.mem.1.1.1)
      ⟨hW.2.1, hyV⟩ inter_subset_left
    obtain ⟨θ', hθ', hθ'e⟩ := exists_faceExt_eq hd hV'.1.1.1 t.mem.1.1.1 inter_subset_right
      hV'.2.1 ⟨t.mem_faces.1, hyθ⟩
    exact ⟨BTriple.cls hd ⟨⟨y, W ∩ t.V, hV', hy1⟩, θ', hθ'⟩,
      ⟨_, rfl, hyθ, ⟨inter_subset_right, t.mem.1.1.2 y hyV, hyx⟩, hθ'e⟩, rfl⟩

omit hd in
lemma reach_eq_self_of_isCenteredAt {V : Set X} {x : X} (h : IsCenteredAt d x V) :
    reach d V x = V :=
  Subset.antisymm (reach_subset V x) fun _ hy => ⟨hy, fun γ hγ => h γ hγ.1⟩

/-- **(2.44) for centred `V`**: `Φ_{(x,V,θ)}` maps `U(x, V, θ)` bijectively onto `θ`. -/
theorem bMap_image_uSet_of_isCenteredAt {t : BTriple hd} (h : IsCenteredAt d t.x t.V) :
    bMap hd '' uSet hd t = t.θ := by
  rw [bMap_image_uSet hd, reach_eq_self_of_isCenteredAt h, inter_eq_left.2 t.mem_faces.1.subset]

theorem phi_bijective_of_isCenteredAt {t : BTriple hd} (h : IsCenteredAt d t.x t.V) :
    Bijective (phi hd t) := by
  refine ⟨phi_injective hd t, fun y => ?_⟩
  have hy : (y : X) ∈ bMap hd '' uSet hd t := by
    rw [bMap_image_uSet_of_isCenteredAt hd h]; exact y.2
  obtain ⟨p, hp, hpy⟩ := hy
  exact ⟨⟨p, hp⟩, Subtype.ext hpy⟩

/-- `V^x` is centred at `x`. -/
theorem isCenteredAt_reach {V : Set X} (hV : IsOpen V) {x : X} (hx : x ∈ V) :
    IsCenteredAt d x (reach d V x) := by
  rintro θ ⟨p, hp, hp1, rfl⟩
  have hxF : x ∈ faceAt d V p := hp.2 _ ⟨isFaceIn_faceAt hp.1 hp1, mem_faceAt_self hp.1 hp1⟩
  have hsub : connectedComponentIn (V ∩ {z | d z = 1}) p ⊆ reach d V x ∩ {z | d z = 1} := by
    intro q hq
    have hq' := connectedComponentIn_subset _ _ hq
    refine ⟨⟨hq'.1, fun γ hγ => ?_⟩, hq'.2⟩
    rw [hγ.1.eq_faceAt_of_mem hd hV hγ.2 hq'.2,
      ← (faceAt_eq_faceAt_iff hd hV hq'.1 hq'.2).2 hq]
    exact hxF
  have hcc := isPreconnected_connectedComponentIn.subset_connectedComponentIn
    (mem_connectedComponentIn (F := V ∩ {z | d z = 1}) ⟨hp.1, hp1⟩) hsub
  exact ⟨mem_reach_self hx, closure_mono hcc hxF.2⟩

/-- `V^x ∈ N_{X,x}` for `V ∈ N_{X,x}`: the centred neighbourhoods are cofinal in `N_{X,x}`. -/
theorem reach_mem_faceStructuredNbhdsAt {V : Set X} {x : X} (hV : V ∈ faceStructuredNbhdsAt d x) :
    reach d V x ∈ faceStructuredNbhdsAt d x :=
  mem_faceStructuredNbhdsAt_of_subset hd hV (isOpen_reach hd hV.1.1.1 x) (mem_reach_self hV.2.1)
    (reach_subset V x)

/-- The fibre `B⁻¹(x)` has `d(x)` points (one class `[x, V, θ]` for each `θ ∈ F_X(x, V)`). -/
theorem encard_bMap_preimage (x : X) : (bMap hd ⁻¹' {x}).encard = d x := by
  classical
  rcases Nat.eq_zero_or_pos (d x) with h0 | hpos
  · rw [h0]
    refine encard_eq_zero.2 (eq_empty_iff_forall_notMem.2 fun p hp => ?_)
    obtain ⟨s, rfl⟩ := BSpace.exists_rep hd p
    have h1 := s.one_le
    simp only [mem_preimage, bMap_cls, mem_singleton_iff] at hp
    rw [hp] at h1; omega
  obtain ⟨V, hV⟩ := faceStructuredNbhdsAt_nonempty hd x
  have hne : (facesThrough d V x).Nonempty := by
    rw [← encard_ne_zero, hV.1.1.2 x hV.2.1]; exact Nat.cast_ne_zero.2 (by omega)
  have : Nonempty (BSpace hd) := ⟨BTriple.cls hd ⟨⟨x, V, hV, hpos⟩, hne.some, hne.some_mem⟩⟩
  let f : Set X → BSpace hd := fun θ =>
    if h : θ ∈ facesThrough d V x then BTriple.cls hd ⟨⟨x, V, hV, hpos⟩, θ, h⟩
    else Classical.arbitrary _
  have hf : ∀ θ (h : θ ∈ facesThrough d V x), f θ = BTriple.cls hd ⟨⟨x, V, hV, hpos⟩, θ, h⟩ :=
    fun θ h => dif_pos h
  have himg : f '' facesThrough d V x = bMap hd ⁻¹' {x} := by
    ext p
    constructor
    · rintro ⟨θ, hθ, rfl⟩; rw [hf θ hθ]; rfl
    · intro hp
      obtain ⟨s, rfl⟩ := BSpace.exists_rep hd p
      simp only [mem_preimage, bMap_cls, mem_singleton_iff] at hp
      have hsV : s.V ∈ faceStructuredNbhdsAt d x := by rw [← hp]; exact s.mem
      have hV' := inter_mem_faceStructuredNbhdsAt hd hV hsV
      have hs : s.θ ∈ facesThrough d s.V x := by rw [← hp]; exact s.mem_faces
      obtain ⟨θ', hθ', hθ'e⟩ :=
        exists_faceExt_eq hd hV'.1.1.1 s.mem.1.1.1 inter_subset_right hV'.2.1 hs
      have hθ := faceExt_mem_facesThrough hd hV.1.1.1 inter_subset_left hθ'
      refine ⟨_, hθ, ?_⟩
      rw [hf _ hθ, BTriple.cls_eq_cls]
      exact ⟨hp.symm, V ∩ s.V, hV', subset_rfl, θ', hθ', rfl, hθ'e⟩
  have hinj : InjOn f (facesThrough d V x) := by
    intro θ₁ h₁ θ₂ h₂ h
    rw [hf θ₁ h₁, hf θ₂ h₂, BTriple.cls_eq_cls] at h
    obtain ⟨-, V'', -, -, θ'', -, e₁, e₂⟩ := h
    exact e₁.symm.trans e₂
  rw [← himg, hinj.encard_image, hV.1.1.2 x hV.2.1]

/-- The image of `B` is `∂X = {d ≥ 1}`. -/
theorem range_bMap : range (bMap hd) = {x | 1 ≤ d x} := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨s, rfl⟩ := BSpace.exists_rep hd p
    exact s.one_le
  · intro hx
    have : (bMap hd ⁻¹' {x}).Nonempty := by
      rw [← encard_ne_zero, encard_bMap_preimage hd]
      exact Nat.cast_ne_zero.2 (by simp only [mem_ofPred_eq] at hx; omega)
    obtain ⟨p, hp⟩ := this
    exact ⟨p, hp⟩

end USet

end TameBoundary

/-! ### Tame M-polyfolds satisfy the corner axioms -/

namespace MPolyfold

open TameBoundary

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)
  {n : ℕ} {W : ScBanach}

/-- **Local pieces in a tame chart.**  Let `φ : V → O` be a chart modelled on the tame retract
`O = r(U)`, `C = T⁻¹([0,∞)ⁿ ⊕ W)`, and `y ∈ V`, `e = φ(y)`.  For small `ε` the sets
`ℓ_i = φ⁻¹(r({z ∈ C | |z − e| < ε, I(z) = {i}}))`, `i ∈ I(e)`, are local pieces of
`{d_X = 1}` at `y` inside a given neighbourhood `N` (Lemma 4.C, `local_face_structure`), and they
are separated in `V`: a preconnected subset of `V ∩ {d_X = 1}` lies in one hyperplane `f_j`
(Lemma 4.A, `subset_coordHyper_of_isPreconnected`) while `ℓ_i ⊆ φ⁻¹(f_i)` has `I = {i}`. -/
theorem exists_localPieces_chart {φ : MChart X} (hφ : P.IsChart φ)
    (R : ScRetraction φ.model.E φ.model.C) (hRO : R.retract = φ.model.O)
    {T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)}
    (hT : φ.model.C = T 0 ⁻¹' quadrant n W 0) (hR : R.IsTameWith T) {y : X} (hy : y ∈ φ.source)
    {N : Set X} (hN : N ∈ 𝓝 y) :
    ∃ L : LocalPieces P.degIndex y N, ∀ S ⊆ φ.source ∩ {z | P.degIndex z = 1},
      IsPreconnected S → ∀ i j, (S ∩ L.piece i).Nonempty → (S ∩ L.piece j).Nonempty → i = j := by
  classical
  have hdeg : ∀ z ∈ φ.source, P.degIndex z = degIndexWith T (φ z) := fun z hz => by
    rw [P.degIndex_eq_chartDegIndex_of_isTameWith hφ R hRO hT hR hz, chartDegIndex,
      degIndex_eq T hT (φ.apply_mem_C hz)]
  set e := φ y with he
  have heO : e ∈ R.retract := by rw [hRO]; exact φ.mapsTo_model y hy
  have heU : e ∈ R.U := R.retract_subset heO
  have heC : e ∈ φ.model.C := φ.apply_mem_C hy
  have hRe : R e = e := R.apply_eq_self_of_mem_retract heO
  set I := zeroSet T e with hI
  have hcard : I.card = P.degIndex y := by rw [hdeg y hy, degIndexWith_eq_card_zeroSet]
  -- the points `p_i` of Lemma 4.C
  have key : ∀ i : Fin n, (T 0 e).1 i = 0 → ∃ p ∈ R.faceStratum, (T 0 p).1 i = 0 ∧
      ∀ᶠ z in 𝓝 e, z ∈ φ.model.C → zeroSet T z = {i} →
        R z ∈ connectedComponentIn R.faceStratum p := by
    intro i hi
    obtain ⟨ε, hε, p, hpS, hpi, -, -, -, hB, -⟩ := local_face_structure hT hR heO hi
    exact ⟨p, hpS, hpi, Filter.mem_of_superset (Metric.ball_mem_nhds e hε)
      fun z hz hzC hzI => hB z ⟨hz, hzC⟩ hzI⟩
  choose! p hpS hpi hp using key
  have hRc : ContinuousOn R R.U := R.isSc1.isSc0.continuousOn_base
  have hRO' : ∀ z ∈ R.U, R z ∈ φ.model.O := fun z hz => by rw [← hRO]; exact R.apply_mem_retract hz
  have hcomp : ContinuousWithinAt (fun z => φ.symm (R z)) R.U e :=
    (φ.continuousOn_invFun (R e) (hRO' e heU)).comp (hRc e heU) hRO'
  have hsy : φ.symm (R e) = y := by rw [hRe]; exact φ.symm_apply_apply hy
  -- the conditions on the radius
  obtain ⟨O₀, hO₀, hUO₀⟩ := R.relOpen.relOpen
  have hG1 : ∀ᶠ z in 𝓝 e, z ∈ φ.model.C → z ∈ R.U :=
    Filter.mem_of_superset (hO₀.mem_nhds (hUO₀ ▸ heU).1) fun z hz hzC => hUO₀ ▸ ⟨hz, hzC⟩
  have hG4 : ∀ᶠ z in 𝓝 e, z ∈ R.U → φ.symm (R z) ∈ N := by
    have := hcomp.tendsto (hsy.symm ▸ hN : N ∈ 𝓝 (φ.symm (R e)))
    obtain ⟨t, ht, hte, hts⟩ := mem_nhdsWithin.1 this
    exact Filter.mem_of_superset (ht.mem_nhds hte) fun z hz hzU => hts ⟨hz, hzU⟩
  have hG3 : ∀ᶠ z in 𝓝 e, ∀ i ∈ I, z ∈ φ.model.C → zeroSet T z = {i} →
      R z ∈ connectedComponentIn R.faceStratum (p i) :=
    (Filter.eventually_all_finset I).2 fun i hi => hp i ((mem_zeroSet T).1 hi)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1
    (hG1.and ((eventually_zeroSet_subset T e).and (hG3.and hG4)))
  -- the pieces
  have hC : Convex ℝ φ.model.C := R.relOpen.isPartialQuadrant.convex
  let A : Fin n → Set (φ.model.E 0) := fun i =>
    {z | z ∈ Metric.ball e ε ∩ φ.model.C ∧ zeroSet T z = {i}}
  have hAU : ∀ i, A i ⊆ R.U := fun i z hz => (hball hz.1.1).1 hz.1.2
  let eqv : Fin (P.degIndex y) ≃ I := ((Finset.equivFin I).trans (finCongr hcard)).symm
  let piece : Fin (P.degIndex y) → Set X := fun k => φ.symm '' (R '' A (eqv k))
  have hpiece : ∀ k, ∀ w ∈ piece k, ∃ z ∈ A (eqv k), w = φ.symm (R z) ∧
      R z ∈ connectedComponentIn R.faceStratum (p (eqv k)) := by
    rintro k _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, rfl, (hball hz.1.1).2.2.1 _ (eqv k).2 hz.1.2 hz.2⟩
  have hccS : ∀ i, connectedComponentIn R.faceStratum (p i) ⊆ R.faceStratum :=
    fun i => connectedComponentIn_subset _ _
  -- the ray `e + t v` with `I(e + t v) = {i}`
  have hray : ∀ i ∈ I, ∀ᶠ t in 𝓝[>] (0 : ℝ),
      e + t • coordVec T (rayDir I i) ∈ φ.model.C ∧
        zeroSet T (e + t • coordVec T (rayDir I i)) = {i} := by
    intro i hi
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    have hcoord : ∀ l, (T 0 (e + t • coordVec T (rayDir I i))).1 l =
        (T 0 e).1 l + t * rayDir I i l := fun l => by
      have h := coord_coordVec (T := T) (rayDir I i) l
      simp only [map_add, map_smul, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul] at h ⊢
      rw [h]
    refine ⟨?_, ?_⟩
    · rw [hT]
      intro l
      rw [hcoord]
      exact add_nonneg (coord_nonneg hT heC l) (mul_nonneg ht.le (rayDir_nonneg I i l))
    · ext l
      rw [mem_zeroSet, Finset.mem_singleton, hcoord]
      constructor
      · intro h0
        by_contra hli
        by_cases hlI : l ∈ I
        · have h1 : (T 0 e).1 l = 0 := (mem_zeroSet T).1 hlI
          have h2 := rayDir_pos hlI hli
          rw [h1, zero_add] at h0
          exact absurd h0 (mul_pos ht h2).ne'
        · have h1 : (T 0 e).1 l ≠ 0 := fun h => hlI ((mem_zeroSet T).2 h)
          rw [rayDir_eq_zero hlI, mul_zero, add_zero] at h0
          exact h1 h0
      · rintro rfl
        rw [(mem_zeroSet T).1 hi, rayDir_self, mul_zero, add_zero]
  refine ⟨{ B := φ.source ∩ φ ⁻¹' Metric.ball e ε
            isOpen_B := φ.continuousOn_toFun.isOpen_inter_preimage φ.isOpen_source
              Metric.isOpen_ball
            mem_B := ⟨hy, Metric.mem_ball_self hε⟩
            B_subset := ?_
            piece := piece
            isPreconnected := ?_
            piece_subset := ?_
            mem_closure := ?_
            cover := ?_ }, ?_⟩
  · rintro w ⟨hw, hwB⟩
    have hwC := φ.apply_mem_C hw
    have hwO : φ w ∈ R.retract := by rw [hRO]; exact φ.mapsTo_model w hw
    have := (hball hwB).2.2.2 ((hball hwB).1 hwC)
    rwa [R.apply_eq_self_of_mem_retract hwO, φ.symm_apply_apply hw] at this
  · intro k
    have hA : IsPreconnected (A (eqv k)) :=
      (convex_ball_inter_zeroSet_eq hT hC e ε (eqv k)).isPreconnected
    exact (hA.image R (hRc.mono (hAU _))).image φ.symm
      (φ.continuousOn_invFun.mono fun _ ⟨z, hz, hzR⟩ => hzR ▸ hRO' z (hAU _ hz))
  · intro k w hw
    obtain ⟨z, hz, rfl, hRz⟩ := hpiece k w hw
    refine ⟨(hball hz.1.1).2.2.2 (hAU _ hz), ?_⟩
    have hRzO := hRO' z (hAU _ hz)
    change P.degIndex (φ.symm (R z)) = 1
    rw [hdeg _ (φ.symm_mapsTo hRzO), φ.apply_symm_apply hRzO]
    exact faceStratum_degIndexWith hT (hccS _ hRz)
  · intro k
    have hi := (eqv k).2
    have hzt : Tendsto (fun t : ℝ => e + t • coordVec T (rayDir I (eqv k))) (𝓝[>] 0) (𝓝 e) := by
      have : Tendsto (fun t : ℝ => e + t • coordVec T (rayDir I (eqv k))) (𝓝 0)
          (𝓝 (e + (0 : ℝ) • coordVec T (rayDir I (eqv k)))) :=
        (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
      rw [zero_smul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hev := hray _ hi
    have hzU : ∀ᶠ t in 𝓝[>] (0 : ℝ), e + t • coordVec T (rayDir I (eqv k)) ∈
        A (eqv k) := by
      filter_upwards [hev, hzt.eventually (Metric.ball_mem_nhds e hε)] with t ht htb
      exact ⟨⟨htb, ht.1⟩, ht.2⟩
    have htU : Tendsto (fun t : ℝ => e + t • coordVec T (rayDir I (eqv k))) (𝓝[>] 0)
        (𝓝[R.U] e) :=
      tendsto_nhdsWithin_iff.2 ⟨hzt, hzU.mono fun t ht => hAU _ ht⟩
    have hlim := hcomp.tendsto.comp htU
    rw [hsy] at hlim
    exact mem_closure_of_tendsto hlim (hzU.mono fun t ht => ⟨_, ⟨_, ht, rfl⟩, rfl⟩)
  · rintro w ⟨⟨hw, hwB⟩, hw1⟩
    change P.degIndex w = 1 at hw1
    rw [hdeg w hw, degIndexWith_eq_card_zeroSet, Finset.card_eq_one] at hw1
    obtain ⟨j, hj⟩ := hw1
    have hjI : j ∈ I := (hball hwB).2.1 (by rw [hj]; exact Finset.mem_singleton_self j)
    have hwO : φ w ∈ R.retract := by rw [hRO]; exact φ.mapsTo_model w hw
    refine mem_iUnion.2 ⟨eqv.symm ⟨j, hjI⟩, ?_⟩
    have hA : φ w ∈ A (eqv (eqv.symm ⟨j, hjI⟩)) := by
      rw [Equiv.apply_symm_apply]; exact ⟨⟨hwB, φ.apply_mem_C hw⟩, hj⟩
    exact ⟨R (φ w), ⟨φ w, hA, rfl⟩, by
      rw [R.apply_eq_self_of_mem_retract hwO, φ.symm_apply_apply hw]⟩
  · -- separation
    intro S hS hSc k k' ⟨w₁, hw₁S, hw₁⟩ ⟨w₂, hw₂S, hw₂⟩
    obtain ⟨z₁, hz₁, rfl, hRz₁⟩ := hpiece k w₁ hw₁
    obtain ⟨z₂, hz₂, rfl, hRz₂⟩ := hpiece k' w₂ hw₂
    have hR₁O := hRO' z₁ (hAU _ hz₁)
    have hR₂O := hRO' z₂ (hAU _ hz₂)
    have hφS : IsPreconnected (φ '' S) :=
      hSc.image φ (φ.continuousOn_toFun.mono fun z hz => (hS hz).1)
    have hφSC : φ '' S ⊆ φ.model.C := by rintro _ ⟨z, hz, rfl⟩; exact φ.apply_mem_C (hS hz).1
    have hφS1 : ∀ z ∈ φ '' S, degIndexWith T z = 1 := by
      rintro _ ⟨z, hz, rfl⟩; rw [← hdeg z (hS hz).1]; exact (hS hz).2
    have hcc₁ : R z₁ ∈ coordHyper T (eqv k) :=
      connectedComponentIn_faceStratum_subset hT (hpi _ ((mem_zeroSet T).1 (eqv k).2)) hRz₁
    have hsub := subset_coordHyper_of_isPreconnected hT hφS hφSC hφS1
      (p := R z₁) ⟨_, hw₁S, φ.apply_symm_apply hR₁O⟩ hcc₁
    have h₂ : φ (φ.symm (R z₂)) ∈ coordHyper T (eqv k) := hsub ⟨_, hw₂S, rfl⟩
    rw [φ.apply_symm_apply hR₂O] at h₂
    have hcc₂ : R z₂ ∈ coordHyper T (eqv k') :=
      connectedComponentIn_faceStratum_subset hT (hpi _ ((mem_zeroSet T).1 (eqv k').2)) hRz₂
    have hz1 : zeroSet T (R z₂) = {(eqv k' : Fin n)} :=
      zeroSet_eq_singleton (faceStratum_degIndexWith hT (hccS _ hRz₂)) hcc₂
    have : (eqv k : Fin n) ∈ zeroSet T (R z₂) := (mem_zeroSet T).2 h₂
    rw [hz1, Finset.mem_singleton] at this
    exact eqv.injective (Subtype.ext this)

/-- **The degeneracy index of a tame M-polyfold satisfies the corner axioms** (Lemma 2.23 and the
local pieces of `exists_localPieces_chart`, with `D` the domain of a tame chart). -/
theorem isCornerIndex_degIndex (hP : P.IsTame) : IsCornerIndex P.degIndex := by
  refine ⟨fun x => lemma_2_23 P x, fun x => ?_⟩
  obtain ⟨φ, hφ, hx, R, hRO, hRt⟩ := IsTame.exists_chart P hP x
  obtain ⟨n, W, T, hT⟩ := φ.model.isPartialQuadrant
  exact ⟨φ.source, φ.isOpen_source, hx, fun y hy N hN =>
    P.exists_localPieces_chart hφ R hRO hT (hRt n W T hT) hy hN⟩

/-! ### The tame M-polyfold `X`: Proposition 2.7.5, Proposition 2.7.7, Definitions 2.7.8–2.7.10 -/

section Tame

open CategoryTheory

/-- The faces of `X` (2021 Definition 2.5.10, `MPolyfold.IsFace`) are the faces of the open set
`X` in the sense of `TameBoundary.IsFaceIn`. -/
theorem isFaceIn_univ_iff {θ : Set X} : IsFaceIn P.degIndex univ θ ↔ P.IsFace θ := by
  simp only [IsFaceIn, faceAt, IsFace, univ_inter, mem_univ, true_and]

/-- **2021 Proposition 2.7.5, p. 78** (new in the 2021 edition): in a tame M-polyfold every `x`
has an open neighbourhood `V` with (1) `d_X(y) ≤ d_X(x)` for `y ∈ V`; (2) every `y ∈ V` lies in
exactly `d_X(y)` faces of `V`; (3) an open `U(x) ⊆ V` such that every face of `V` containing a
point of `U(x)` contains `x`.  The faces of `V` are those of `V` with the induced structure, whose
degeneracy index is `d_X|V`. -/
theorem proposition_2_7_5_2021 (hP : P.IsTame) (x : X) :
    ∃ V, IsOpen V ∧ x ∈ V ∧ (∀ y ∈ V, P.degIndex y ≤ P.degIndex x) ∧
      (∀ y ∈ V, (facesThrough P.degIndex V y).encard = P.degIndex y) ∧
      ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ V ∧
        ∀ θ, IsFaceIn P.degIndex V θ → ∀ y ∈ U, y ∈ θ → x ∈ θ :=
  proposition_2_7_5 (P.isCornerIndex_degIndex hP) x

/-- **2021 Proposition 2.7.7, p. 80** (new in the 2021 edition), for a tame `X`: (1) every
`N_{X,x}` is nonempty, so `N_X` covers `X`; (2) a nonempty open subset of a `V ∈ N_X` belongs to
`N_X`; (3) nonempty intersections of members of `N_X` belong to `N_X`, and `N_{X,x}` is closed
under intersections. -/
theorem proposition_2_7_7_2021 (hP : P.IsTame) :
    (∀ x, (faceStructuredNbhdsAt P.degIndex x).Nonempty) ∧
      ⋃₀ faceStructuredNbhds P.degIndex = univ ∧
      (∀ U V, V ∈ faceStructuredNbhds P.degIndex → IsOpen U → U.Nonempty → U ⊆ V →
        U ∈ faceStructuredNbhds P.degIndex) ∧
      (∀ V V', V ∈ faceStructuredNbhds P.degIndex → V' ∈ faceStructuredNbhds P.degIndex →
        (V ∩ V').Nonempty → V ∩ V' ∈ faceStructuredNbhds P.degIndex) ∧
      ∀ x V V', V ∈ faceStructuredNbhdsAt P.degIndex x →
        V' ∈ faceStructuredNbhdsAt P.degIndex x → V ∩ V' ∈ faceStructuredNbhdsAt P.degIndex x :=
  ⟨faceStructuredNbhdsAt_nonempty (P.isCornerIndex_degIndex hP),
    sUnion_faceStructuredNbhds (P.isCornerIndex_degIndex hP),
    fun _ _ hV hU hne hUV => mem_faceStructuredNbhds_of_subset (P.isCornerIndex_degIndex hP) hV hU
      hne hUV,
    fun _ _ hV hV' hne => inter_mem_faceStructuredNbhds (P.isCornerIndex_degIndex hP) hV hV' hne,
    fun _ _ _ hV hV' => inter_mem_faceStructuredNbhdsAt (P.isCornerIndex_degIndex hP) hV hV'⟩

/-- **2021 Definition 2.7.8, p. 80** (new in the 2021 edition): the **local boundary structure
category** `L_X` of the tame `X` (objects `(x, V)`, `x ∈ ∂X`, `V ∈ N_{X,x}`; at most one morphism,
`TameBoundary.IsMor`), a thin category through `Preorder.smallCategory`. -/
abbrev LocalBoundaryCategory (hP : P.IsTame) : Type u := LObj (P.isCornerIndex_degIndex hP)

/-- **2021 Definition 2.7.9, p. 81** (new in the 2021 edition): the **boundary structure functor**
`F_X : L_X → SET`. -/
def boundaryStructureFunctor (hP : P.IsTame) : P.LocalBoundaryCategory hP ⥤ Type u :=
  boundaryFunctor (P.isCornerIndex_degIndex hP)

/-- **2021 Definition 2.7.10, p. 81** (new in the 2021 edition): the set `bX` of classes
`[x, V, θ]` of admissible boundary triples. -/
abbrev TameBoundarySpace (hP : P.IsTame) : Type u := BSpace (P.isCornerIndex_degIndex hP)

/-- **2021 Definition 2.7.10**: the map `B : bX → X`, `[x, V, θ] ↦ x`. -/
def tameBoundaryMap (hP : P.IsTame) : P.TameBoundarySpace hP → X :=
  bMap (P.isCornerIndex_degIndex hP)

/-- `B` has image `∂X` (2021 Definition 2.4.5, `MPolyfold.boundary`), and `x` has exactly `d_X(x)`
preimages (the fibre count behind 2021 Theorem 2.7.13 (4)). -/
theorem range_tameBoundaryMap (hP : P.IsTame) : range (P.tameBoundaryMap hP) = P.boundary :=
  range_bMap _

theorem encard_tameBoundaryMap_preimage (hP : P.IsTame) (x : X) :
    (P.tameBoundaryMap hP ⁻¹' {x}).encard = P.degIndex x :=
  encard_bMap_preimage _ x

end Tame

/-! ### Tame sub-M-polyfolds (2021 Definitions 2.5.18 and 2.5.19) -/

section TameSub

/-- **2021 Definition 2.5.18, p. 62** (new in the 2021 edition): the structure induced on the
sub-M-polyfold `Y` (2021 Definition 2.3.18; preprint Proposition 2.21, `subPolyfold`) **is tame**:
it admits an equivalent atlas with tame models (2021 Definition 2.5.7, `MPolyfold.IsTame`).  The
subspace `Y` is paracompact by `paracompactSpace_subtype`. -/
def HasTameInducedStructure (Y : Set X) : Prop :=
  ∃ hY : P.IsSubMPolyfold Y,
    letI := P.paracompactSpace_subtype Y
    (subPolyfold hY).IsTame

omit [T2Space X] [ParacompactSpace X] in
private lemma isScSubspace_bot' (E : ScBanach) : E.IsScSubspace ⊥ := by
  refine ⟨by simp, fun m x hx => ?_⟩
  have hx0 : x = 0 := by
    rw [SetLike.mem_coe, ScBanach.mem_levelSub, Submodule.mem_bot] at hx
    exact E.toBase_injective m (by rw [hx, map_zero])
  rw [hx0]
  exact subset_closure ⟨by simp, by
    simp only [ScScale.smoothLvl, mem_preimage, map_zero, SetLike.mem_coe]; exact zero_mem _⟩

omit [T2Space X] [ParacompactSpace X] in
private lemma levelSub_bot' (E : ScBanach) (m : ℕ) : E.levelSub ⊥ m = ⊥ := by
  ext x
  rw [ScBanach.mem_levelSub, Submodule.mem_bot, Submodule.mem_bot]
  exact ⟨fun h => E.toBase_injective m (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩

/-- **2021 Definition 2.5.19 (3) in a chart**: for retracts `Q ⊆ O` in `C`, a presentation `T` of
`C` and a level-`1` point `z` of `Q`, the tangent space `T_zQ` has in `T_zO` an sc-complement
`A` contained in the reduced tangent space `T_z^R O = T_zO ∩ E_z` (2021 Definitions 2.4.7, 2.5.8):
an sc-subspace `A ⊆ T_zO ∩ E_z` with `(T_zO)_m = (T_zQ)_m ⊕ A_m` on every level.  This is the
same condition as Chapter 4's `IsGeneralPositionRetractAt` (restated here so that Chapter 2 does
not import Chapter 4). -/
def HasReducedComplementAt {E : ScBanach} {n : ℕ} {W : ScBanach} (C O Q : Set (E 0))
    (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (z : E 1) : Prop :=
  ∃ N M A : Submodule ℝ (E 0), (N : Set (E 0)) = tangentSpace E C Q z ∧
    (M : Set (E 0)) = tangentSpace E C O z ∧ A ≤ M ⊓ minimalSubspaceWith T (E.toBase 1 z) ∧
    E.IsScSubspace A ∧ ∀ m, Disjoint (E.levelSub N m) (E.levelSub A m) ∧
      E.levelSub N m ⊔ E.levelSub A m = E.levelSub M m

omit [T2Space X] [ParacompactSpace X] in
/-- `T_zO` has the sc-complement `A = 0` in itself. -/
theorem hasReducedComplementAt_self {E : ScBanach} {n : ℕ} {W : ScBanach} {C : Set (E 0)}
    (R : ScRetraction E C) (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) {z : E 1}
    (hz : z ∈ E.lvlSet R.retract 1) : HasReducedComplementAt C R.retract R.retract T z := by
  obtain ⟨N, hN⟩ : ∃ N : Submodule ℝ (E 0), (N : Set (E 0)) = tangentSpace E C R.retract z :=
    ⟨_, (tangentSpace_eq_coe_submodule R hz).symm⟩
  refine ⟨N, N, ⊥, hN, hN, bot_le, isScSubspace_bot' E, fun m => ?_⟩
  rw [levelSub_bot' E m]
  exact ⟨disjoint_bot_right, sup_bot_eq _⟩

/-- **2021 Definition 2.5.19, p. 63** (new in the 2021 edition), the data at a point: an open
`V` and an sc-smooth retraction `r : V → V` (a `SubData`, so (1) `r(V) = Y ∩ V`) with
(2) `d_X(r(x)) = d_X(x)` on `V`, and (3) at every smooth `y ∈ Y ∩ V`, `T_yY` has an
sc-complement in `T_yX` inside `T_y^R X`.  As `T_yX` carries no linear structure here (gap G.7),
(3) is stated in a chart `φ ∋ y` with a presentation `T` and the level-`1` point `z` over
`φ(y)`: `HasReducedComplementAt` for `O` and the chart model `Q = φ(W ∩ Y)` of `Y`
(`W = V ∩ dom φ ∩ r⁻¹(V ∩ dom φ)`, `SubData.shrink`). -/
structure TameSubData (Y : Set X) extends P.SubData Y where
  degIndex_apply : ∀ x ∈ V, P.degIndex (r x) = P.degIndex x
  complement : ∀ y ∈ Y ∩ V, y ∈ P.smoothSet → ∃ (φ : MChart X) (n : ℕ) (W : ScBanach)
    (T : ScIso φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)) (z : φ.model.E 1),
    P.IsChart φ ∧ y ∈ φ.source ∧ φ.model.C = T 0 ⁻¹' quadrant n W 0 ∧
      φ.model.E.toBase 1 z = φ y ∧
      HasReducedComplementAt φ.model.C φ.model.O
        (φ '' ((V ∩ φ.source) ∩ r ⁻¹' (V ∩ φ.source) ∩ Y)) T z

/-- **2021 Definition 2.5.19, p. 63**: `Y` is a **tame sub-M-polyfold** of the tame M-polyfold
`X` if every `y ∈ Y` lies in the domain of a `TameSubData` (the retraction `r` is then a tame
sc-smooth retraction).  `Y` is then a sub-M-polyfold (`IsTameSubMPolyfold.isSubMPolyfold`). -/
def IsTameSubMPolyfold (Y : Set X) : Prop :=
  P.IsTame ∧ ∀ y ∈ Y, ∃ d : P.TameSubData Y, y ∈ d.V

variable {P} in
theorem IsTameSubMPolyfold.isSubMPolyfold {Y : Set X} (h : P.IsTameSubMPolyfold Y) :
    P.IsSubMPolyfold Y := fun y hy => by
  obtain ⟨d, hyd⟩ := h.2 y hy
  exact ⟨d.V, d.isOpen, hyd, d.r, d.mapsTo, d.isScSmoothOn, d.idem, d.image⟩

/-- The data `(V, r) = (X, id)` of `Y = X`. -/
def subDataUniv : P.SubData univ where
  V := univ
  r := id
  isOpen := isOpen_univ
  mapsTo := mapsTo_id _
  isScSmoothOn := isScSmoothMap_id
  idem _ _ := rfl
  image := by simp

lemma subDataUniv_shrink (φ : MChart X) : (P.subDataUniv).shrink φ = φ.source := by
  ext x
  simp [SubData.shrink, subDataUniv]

/-- **Satisfiability of Definition 2.5.18**: the structure induced on `Y = X` from a tame `X` is
tame (the sub-charts of `(X, id)` built on tame charts of `X` have the same tame models). -/
theorem hasTameInducedStructure_univ (hP : P.IsTame) : P.HasTameInducedStructure univ := by
  refine ⟨P.isSubMPolyfold_univ, ?_⟩
  have := P.paracompactSpace_subtype (univ : Set X)
  refine isTame_of_forall_exists_chart _ fun a => ?_
  obtain ⟨φ, hφ, ha, ht⟩ := IsTame.exists_chart P hP a.1
  refine ⟨subChart P.subDataUniv hφ a, subPolyfold_isChart _ P.subDataUniv hφ a, ?_, ?_⟩
  · change a.1 ∈ (P.subDataUniv).shrink φ
    rw [subDataUniv_shrink]; exact ha
  · rw [subChart_model_O, subDataUniv_shrink, inter_univ, φ.image_source]
    exact ht

/-- **Satisfiability of Definition 2.5.19**: in a tame `X`, `Y = X` is a tame sub-M-polyfold
(`r = id`; in every chart `Q = O` and `A = 0`). -/
theorem isTameSubMPolyfold_univ (hP : P.IsTame) : P.IsTameSubMPolyfold univ := by
  refine ⟨hP, fun y _ => ⟨⟨P.subDataUniv, fun _ _ => rfl, fun y _ hys => ?_⟩, mem_univ y⟩⟩
  obtain ⟨φ, hφ, hy⟩ := P.exists_isChart_mem_source y
  obtain ⟨n, W, T, hT⟩ := φ.model.isPartialQuadrant
  have hs : φ y ∈ φ.model.E.smooth := by
    rw [smoothSet, mem_iInter] at hys
    refine (ScScale.mem_smooth_iff _).2 fun m => ?_
    exact (P.mem_levelSet_iff hφ hy).1 (hys m)
  obtain ⟨z, hz, -⟩ := exists_smoothLvl_one_of_mem_smooth hs
  obtain ⟨R, hR⟩ := φ.model.isScRetract
  refine ⟨φ, n, W, T, z, hφ, hy, hT, hz, ?_⟩
  have hQ : φ '' ((univ ∩ φ.source) ∩ id ⁻¹' (univ ∩ φ.source) ∩ univ) = φ.model.O := by
    rw [← φ.image_source]; congr 1; ext x; simp
  change HasReducedComplementAt φ.model.C φ.model.O
    (φ '' ((univ ∩ φ.source) ∩ id ⁻¹' (univ ∩ φ.source) ∩ univ)) T z
  rw [hQ, ← hR]
  exact hasReducedComplementAt_self R T (by
    rw [ScBanach.mem_lvlSet, hz, hR]; exact φ.mapsTo_model y hy)

end TameSub

end MPolyfold

/-! ### Non-vacuity -/

namespace TameBoundary

variable {X : Type u} [TopologicalSpace X]

/-- **The corner axioms are satisfiable**: `d ≡ 0` (no boundary) satisfies them. -/
theorem isCornerIndex_zero : IsCornerIndex (fun _ : X => 0) where
  eventually_le _ := Filter.Eventually.of_forall fun _ => le_rfl
  exists_pieces _ := ⟨univ, isOpen_univ, mem_univ _, fun y _ N hN =>
    ⟨{ B := interior N
       isOpen_B := isOpen_interior
       mem_B := mem_interior_iff_mem_nhds.2 hN
       B_subset := interior_subset
       piece := Fin.elim0
       isPreconnected := fun i => i.elim0
       piece_subset := fun i => i.elim0
       mem_closure := fun i => i.elim0
       cover := fun _ h => absurd h.2 (by simp) }, fun _ _ _ i => i.elim0⟩⟩

end TameBoundary

namespace MPolyfold

open TameBoundary

/-! #### The quadrant `[0,∞)ⁿ ⊕ W` -/

/-- The quadrant `[0,∞)ⁿ ⊕ W` is relatively open in itself. -/
lemma isRelOpenInQuadrant_quadrant (n : ℕ) (W : ScBanach) :
    IsRelOpenInQuadrant ((ScBanach.const (Fin n → ℝ)).prod W) (quadrant n W 0)
      (quadrant n W 0) :=
  ⟨⟨n, W, ScIso.refl _, by ext; rfl⟩, univ, isOpen_univ, (univ_inter _).symm⟩

lemma zero_mem_quadrant (n : ℕ) (W : ScBanach) : (0 : ((ScBanach.const (Fin n → ℝ)).prod W) 0) ∈
    quadrant n W 0 := fun _ => le_rfl

lemma quadrant_nonempty (n : ℕ) (W : ScBanach) : (quadrant n W 0).Nonempty :=
  ⟨0, zero_mem_quadrant n W⟩

/-- The quadrant `[0,∞)ⁿ ⊕ W` as an M-polyfold (one chart, the identity). -/
def quadrantPolyfold (n : ℕ) (W : ScBanach) : MPolyfold (quadrant n W 0) :=
  (isRelOpenInQuadrant_quadrant n W).toMPolyfold (quadrant_nonempty n W)

/-- The quadrant M-polyfold is tame (its chart has the identity retraction, which is tame). -/
theorem quadrantPolyfold_isTame (n : ℕ) (W : ScBanach) : (quadrantPolyfold n W).IsTame := by
  refine isTame_of_forall_exists_chart _ fun a => ⟨_,
    (isRelOpenInQuadrant_quadrant n W).selfChart_isChart (quadrant_nonempty n W), mem_univ a,
    ScRetraction.id (isRelOpenInQuadrant_quadrant n W), image_id _,
    ScRetraction.id_isTame (isRelOpenInQuadrant_quadrant n W)⟩

/-- The corner `0` of `[0,∞)ⁿ ⊕ W` has degeneracy index `n` (2021 Corollary 2.4.13, preprint
Corollary 2.32, `corollary_2_32`). -/
theorem quadrantPolyfold_degIndex_zero (n : ℕ) (W : ScBanach) :
    (quadrantPolyfold n W).degIndex ⟨0, zero_mem_quadrant n W⟩ = n := by
  rw [quadrantPolyfold, corollary_2_32 (isRelOpenInQuadrant_quadrant n W) (quadrant_nonempty n W),
    degIndex_quadrant (zero_mem_quadrant n W), quadrantDeg_zero]

/-- **Non-vacuity of the tame boundary**: for the tame quadrant `[0,∞)ⁿ ⊕ W`, the corner `0` has
exactly `n` preimages under `B : bX → X`; in particular `bX` is nonempty for `n ≥ 1`. -/
theorem quadrantPolyfold_encard_preimage (n : ℕ) (W : ScBanach) :
    ((quadrantPolyfold n W).tameBoundaryMap (quadrantPolyfold_isTame n W) ⁻¹'
      {⟨0, zero_mem_quadrant n W⟩}).encard = n := by
  rw [encard_tameBoundaryMap_preimage, quadrantPolyfold_degIndex_zero]

theorem quadrantPolyfold_tameBoundarySpace_nonempty (n : ℕ) (W : ScBanach) (hn : 1 ≤ n) :
    Nonempty ((quadrantPolyfold n W).TameBoundarySpace (quadrantPolyfold_isTame n W)) := by
  have h := quadrantPolyfold_encard_preimage n W
  obtain ⟨p, -⟩ : (((quadrantPolyfold n W).tameBoundaryMap (quadrantPolyfold_isTame n W)) ⁻¹'
      {⟨0, zero_mem_quadrant n W⟩}).Nonempty := by
    rw [← Set.encard_pos, h]; exact_mod_cast hn
  exact ⟨p⟩

/-- **Non-vacuity of Definitions 2.5.18 and 2.5.19**: `Y = [0,∞)ⁿ ⊕ W` inside itself. -/
theorem quadrantPolyfold_univ (n : ℕ) (W : ScBanach) :
    (quadrantPolyfold n W).HasTameInducedStructure univ ∧
      (quadrantPolyfold n W).IsTameSubMPolyfold univ :=
  ⟨hasTameInducedStructure_univ _ (quadrantPolyfold_isTame n W),
    isTameSubMPolyfold_univ _ (quadrantPolyfold_isTame n W)⟩

end MPolyfold

end Polyfold
