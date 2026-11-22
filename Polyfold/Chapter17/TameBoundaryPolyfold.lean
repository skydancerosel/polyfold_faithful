import Polyfold.Chapter17.TameBoundaryTopology
import Polyfold.Chapter17.OverlappingUniformizers
import Polyfold.Chapter11.EpEquivalenceGeometryFaces
import Polyfold.Chapter11.FaceIntersectionCounterexample

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.4 (pp. 809–811): **the polyfold structure of the tame boundary**, Theorem 17.4.26 and the
displays (17.82)–(17.84).

## The text, paraphrased

(p. 809) For `[α, Ψ, U(ō), θ]` and every `Ψ ∈ F(α)` and every choice of a good open neighbourhood
`U(ō)` the construction gives `Ψ_θ`; these form `F_bC([α, Ψ, U(ō), θ])`. With the transition
construction `M` of Theorem 17.4.16: (Theorem 17.4.26) for a tame polyfold `(C, F, M)` the tame
boundary `bC`, in a natural way a GCT, has a natural polyfold structure `(F_bC, M)`.
(pp. 810–811) The forgetful functor `B : bC → C` fits, for `Ψ ∈ F(α)` and `U(ō)`, into the
commutative square (17.82) `B ∘ Ψ̂ = Ψ ∘ F` with `Θ = ⊔_θ θ`; `F` is sc-smooth on objects (the
inclusion `θ → O`) and on morphisms (`M(Ψ_θ, Ψ_{θ'}) → M(Ψ, Ψ)*_{θ,θ'}` is an sc-diffeomorphism
onto a sub-M-polyfold). With `V(ō)` in place of `O` (17.83), `F` is surjective on objects and
`|B|⁻¹(|Ψ(V)|) = |Ψ̂(Θ)|`; for two such squares (17.84) there is an sc-smooth local embedding
`M(Ψ̂, Ψ̂') → M(Ψ, Ψ')` compatible with the structure maps.

## What is formalized (namespace `Polyfold.GCT.PolyfoldConstruction`)

* `bdryGCT` (`bC` with the metrizable topology `T_bC` of Theorem 17.4.19, a GCT), `FaceData`
  (the data `(Ψ, ō, U(ō), θ)` with `G` fixing `ō`), `FaceData.unif` (`Ψ_θ` as a local uniformizer
  of `bdryGCT`: Lemma 17.4.6 and Lemma 17.4.20).
* **Theorem 17.4.26**: `bdryF` (`F_bC`), `bdryConstruction` (the polyfold structure, built from
  the M-polyfolds `M(Ψ_θ, Ψ'_{θ'})` of Definition 17.4.14 and Theorem 17.4.16),
  `hasUniformizers_bdryConstruction`, and **`theorem_17_4_26`** (`F_bC(ᾱ)` consists of the
  `Ψ_θ` at `ᾱ`, and `M(Ψ_θ, Ψ'_{θ'})` is identified with the sub-M-polyfold `M(Ψ, Ψ')*_{θ,θ'}`,
  keeping morphisms and objects).
* **(17.82)–(17.84)** (namespace `…GoodNbhd`): `display_17_82` (`F` on objects and morphisms,
  `B ∘ Ψ̂ = Ψ ∘ F`), `display_17_83` (`⋃ θ = U(ō)` and `|B|⁻¹(|Ψ(V(ō))|) = ⋃_θ |Ψ_θ(θ)|`),
  `display_17_84` (`M(Ψ_θ, Ψ'_{θ'}) → M(Ψ, Ψ')` is injective with image `M(Ψ, Ψ')*_{θ,θ'}`, a local
  sc-diffeomorphism onto it, sc-smooth, and compatible with `s`, `t` and `B`).
* **Witness with a non-trivial group**: `swapConstruction`, the polyfold `ℤ/2 ⋉ ([0,∞)² ⊕ W)`
  (`−1` exchanging the coordinates) with `F(x)` the inclusion of `[0,∞)² ⊕ W` (group `ℤ/2`) on the
  diagonal and the inclusions of `{p₀ < p₁}`, `{p₁ < p₀}` (trivial group) off it;
  `swap_tameBoundary_witness`: all hypotheses of this section hold, the corner uniformizer has the
  group `ℤ/2` acting non-trivially, `−1` exchanges the two faces of a good neighbourhood of the
  corner, and the two face uniformizers have the same image in `|bC|`; `swap_theorem_17_4_26`.

## Readings

* `bdryGCT` and `bdryConstruction` carry the standing hypotheses of §17.4: tameness, `F(α) ≠ ∅`,
  `Ψ̂` continuous (`HatContinuous`) and `G` fixing `ō` (`IsCentred`), all met by
  `swapConstruction` (with a non-trivial group) and by the quadrant polyfold.
* "For all possible choices of `U(ō)`": `F_bC(ᾱ)` contains `Ψ_θ` for every `Ψ ∈ F(α)`, every
  `ō` with `Ψ(ō) = α`, every good open neighbourhood and every face `θ` with `Ψ_θ(ō) = ᾱ`.
* The transition M-polyfold of `F_bC` is that of Definition 17.4.14 for the data chosen for each
  `L ∈ F_bC` (`faceDataOf`, with `L = Ψ_θ`).
* (17.83): `F` maps the objects of `Θ` onto `U(ō) = V(ō) ∩ ∂O`, the part of `V(ō)` lying over
  `∂C`; we read "surjective on objects" in this sense (`⋃₀ V.faces = V.bdry`), and `|B|` is `σ`
  of (17.76).
* (17.84) is stated for one pair of faces `θ, θ'`; the disjoint unions over all faces are not
  formed as M-polyfolds, the maps being componentwise.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter TopologicalSpace Pointwise

noncomputable section

universe u

namespace Polyfold

open TameBoundary

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} {S : C.PolyfoldConstruction} {hT : S.IsTame} {hS : S.HasUniformizers}

variable (hT hS) in
/-- **The tame boundary `bC` as a GCT** (2021 p. 809): the groupoidal category `bC` with the
metrizable topology `T_bC` (Theorem 17.4.19). -/
def bdryGCT (hc : S.HatContinuous) (hcent : S.IsCentred) : GCT.{u} where
  toGroupoidalCategory := S.bdryCategory hT hS
  top := bdryTopology hT hS
  metrizable := metrizableSpace_bdryOrbit hT hS hc hcent

variable (S) in
/-- The data `(Ψ, ō, U(ō), θ)` of a face uniformizer `Ψ_θ`, with `G` fixing `ō`. -/
structure FaceData : Type (u + 1) where
  /-- The uniformizer `Ψ`. -/
  Ψ : S.Unif
  /-- The point `ō`. -/
  o : Ψ.1.O
  /-- The good open neighbourhood `U(ō)`. -/
  V : S.GoodNbhd Ψ o
  fix : Ψ.1.FixesPoint o
  /-- The face `θ ∈ F_{U(ō)}`. -/
  θ : Set Ψ.1.O
  hθ : θ ∈ V.faces

variable (hT hS) in
/-- **The local uniformizer `Ψ_θ : G_θ ⋉ θ → bC`** of the GCT `bC` (2021 Lemma 17.4.6 and
Lemma 17.4.20): `θ` with its structure as a sub-M-polyfold of `O`, `G_θ` acting by
sc-diffeomorphisms, `Ψ_θ` injective on objects and fully faithful, `|Ψ_θ|` an open embedding. -/
def FaceData.unif (hc : S.HatContinuous) (hcent : S.IsCentred) (d : S.FaceData) :
    (S.bdryGCT hT hS hc hcent).LocalUniformizer where
  O := d.θ
  P := d.V.faceSubPolyfold hT d.hθ
  G := faceStabilizer d.Ψ d.θ
  smooth_smul := d.V.isScSmoothMap_faceStabilizer_smul hT d.hθ
  functor := d.V.faceFunctor hT hS hc d.fix d.hθ
  injective_obj := (d.V.lemma_17_4_6 hc d.fix d.hθ).1
  full := (d.V.lemma_17_4_6 hc d.fix d.hθ).2.1
  faithful := (d.V.lemma_17_4_6 hc d.fix d.hθ).2.2
  isOpenEmbedding_orbitMap := d.V.lemma_17_4_20 hT hS hc d.fix d.hθ

section Construction

variable (hc : S.HatContinuous) (hcent : S.IsCentred)

variable (hT hS) in
/-- **`F_bC(ᾱ)`** (2021 p. 809): the `Ψ_θ` constructed from the `Ψ ∈ F(α)` after choices of good
open neighbourhoods `U(ō)`, with `Ψ_θ(ō) = ᾱ`. -/
def bdryF (ᾱ : S.BObj hT hS) : Set (S.bdryGCT hT hS hc hcent).LocalUniformizer :=
  {L | ∃ d : S.FaceData, d.Ψ.1 ∈ S.F ᾱ.α ∧
    d.V.faceObj hT hS d.hθ d.o (d.V.mem_of_mem_faces d.hθ) = ᾱ ∧ L = d.unif hT hS hc hcent}

theorem exists_faceData (L : @GCT.Unif (S.bdryGCT hT hS hc hcent) (S.bdryF hT hS hc hcent)) :
    ∃ d : S.FaceData, L.1 = d.unif hT hS hc hcent := by
  obtain ⟨L, ᾱ, d, -, -, rfl⟩ := L
  exact ⟨d, rfl⟩

/-- The data `d` chosen for `L ∈ F_bC` with `L = Ψ_θ`. -/
def faceDataOf (L : @GCT.Unif (S.bdryGCT hT hS hc hcent) (S.bdryF hT hS hc hcent)) : S.FaceData :=
  (exists_faceData hc hcent L).choose

theorem faceDataOf_eq (L : @GCT.Unif (S.bdryGCT hT hS hc hcent) (S.bdryF hT hS hc hcent)) :
    L.1 = (faceDataOf hc hcent L).unif hT hS hc hcent :=
  (exists_faceData hc hcent L).choose_spec

variable (hT hS) in
/-- The topology of `M(L, L')` for `L = Ψ_θ`, `L' = Ψ'_{θ'}`. -/
@[instance_reducible]
def ftrTopOf : ∀ (L L' : (S.bdryGCT hT hS hc hcent).LocalUniformizer) (d d' : S.FaceData),
    L = d.unif hT hS hc hcent → L' = d'.unif hT hS hc hcent → TopologicalSpace (L.Trans L')
  | _, _, d, d', rfl, rfl =>
    (inferInstance : TopologicalSpace (d.V.FTr hT hS d'.V d.hθ d'.hθ))

variable (hT hS) in
theorem ftrT2Of : ∀ (L L' : (S.bdryGCT hT hS hc hcent).LocalUniformizer) (d d' : S.FaceData)
    (h : L = d.unif hT hS hc hcent) (h' : L' = d'.unif hT hS hc hcent),
    @T2Space (L.Trans L') (ftrTopOf hT hS hc hcent L L' d d' h h')
  | _, _, d, d', rfl, rfl => (inferInstance : T2Space (d.V.FTr hT hS d'.V d.hθ d'.hθ))

variable (hT hS) in
theorem ftrParaOf : ∀ (L L' : (S.bdryGCT hT hS hc hcent).LocalUniformizer) (d d' : S.FaceData)
    (h : L = d.unif hT hS hc hcent) (h' : L' = d'.unif hT hS hc hcent),
    @ParacompactSpace (L.Trans L') (ftrTopOf hT hS hc hcent L L' d d' h h')
  | _, _, d, d', rfl, rfl => (inferInstance : ParacompactSpace (d.V.FTr hT hS d'.V d.hθ d'.hθ))

variable (hT hS) in
/-- The M-polyfold `M(L, L')` for `L = Ψ_θ`, `L' = Ψ'_{θ'}`: the natural structure
(Definition 17.4.14). -/
def ftrMOf : ∀ (L L' : (S.bdryGCT hT hS hc hcent).LocalUniformizer) (d d' : S.FaceData)
    (h : L = d.unif hT hS hc hcent) (h' : L' = d'.unif hT hS hc hcent),
    @MPolyfold (L.Trans L') (ftrTopOf hT hS hc hcent L L' d d' h h')
      (ftrT2Of hT hS hc hcent L L' d d' h h') (ftrParaOf hT hS hc hcent L L' d d' h h')
  | _, _, d, d', rfl, rfl => d.V.ftrPolyfold hT hS d'.V d.hθ d'.hθ

variable (hT hS) in
theorem ftrSrcOf : ∀ (L L' : (S.bdryGCT hT hS hc hcent).LocalUniformizer) (d d' : S.FaceData)
    (h : L = d.unif hT hS hc hcent) (h' : L' = d'.unif hT hS hc hcent),
    letI := ftrTopOf hT hS hc hcent L L' d d' h h'
    letI := ftrT2Of hT hS hc hcent L L' d d' h h'
    letI := ftrParaOf hT hS hc hcent L L' d d' h h'
    (ftrMOf hT hS hc hcent L L' d d' h h').IsLocalScDiffeo L.P GroupoidStr.TransitionSet.src
  | _, _, d, d', rfl, rfl => d.V.ftr_isLocalScDiffeo_src hT hS d'.V d.hθ d'.hθ

variable (hT hS) in
theorem ftrTgtOf : ∀ (L L' : (S.bdryGCT hT hS hc hcent).LocalUniformizer) (d d' : S.FaceData)
    (h : L = d.unif hT hS hc hcent) (h' : L' = d'.unif hT hS hc hcent),
    letI := ftrTopOf hT hS hc hcent L L' d d' h h'
    letI := ftrT2Of hT hS hc hcent L L' d d' h h'
    letI := ftrParaOf hT hS hc hcent L L' d d' h h'
    (ftrMOf hT hS hc hcent L L' d d' h h').IsLocalScDiffeo L'.P GroupoidStr.TransitionSet.tgt
  | _, _, d, d', rfl, rfl => d.V.ftr_isLocalScDiffeo_tgt hT hS d'.V d.hθ d'.hθ

variable (hT hS) in
theorem ftrUnitOf : ∀ (L : (S.bdryGCT hT hS hc hcent).LocalUniformizer) (d : S.FaceData)
    (h : L = d.unif hT hS hc hcent),
    letI := ftrTopOf hT hS hc hcent L L d d h h
    letI := ftrT2Of hT hS hc hcent L L d d h h
    letI := ftrParaOf hT hS hc hcent L L d d h h
    L.P.IsScSmoothMap (ftrMOf hT hS hc hcent L L d d h h) GroupoidStr.TransitionSet.unit
  | _, d, rfl => d.V.ftr_isScSmoothMap_unit hT hS d.hθ

variable (hT hS) in
theorem ftrInvOf : ∀ (L L' : (S.bdryGCT hT hS hc hcent).LocalUniformizer) (d d' : S.FaceData)
    (h : L = d.unif hT hS hc hcent) (h' : L' = d'.unif hT hS hc hcent),
    letI := ftrTopOf hT hS hc hcent L L' d d' h h'
    letI := ftrT2Of hT hS hc hcent L L' d d' h h'
    letI := ftrParaOf hT hS hc hcent L L' d d' h h'
    letI := ftrTopOf hT hS hc hcent L' L d' d h' h
    letI := ftrT2Of hT hS hc hcent L' L d' d h' h
    letI := ftrParaOf hT hS hc hcent L' L d' d h' h
    (ftrMOf hT hS hc hcent L L' d d' h h').IsScSmoothMap (ftrMOf hT hS hc hcent L' L d' d h' h)
      GroupoidStr.TransitionSet.inv
  | _, _, d, d', rfl, rfl => d.V.ftr_isScSmoothMap_inv hT hS d'.V d.hθ d'.hθ

variable (hT hS) in
theorem ftrMulOf : ∀ (L L' L'' : (S.bdryGCT hT hS hc hcent).LocalUniformizer)
    (d d' d'' : S.FaceData) (h : L = d.unif hT hS hc hcent) (h' : L' = d'.unif hT hS hc hcent)
    (h'' : L'' = d''.unif hT hS hc hcent),
    letI := ftrTopOf hT hS hc hcent L' L'' d' d'' h' h''
    letI := ftrT2Of hT hS hc hcent L' L'' d' d'' h' h''
    letI := ftrParaOf hT hS hc hcent L' L'' d' d'' h' h''
    letI := ftrTopOf hT hS hc hcent L L' d d' h h'
    letI := ftrT2Of hT hS hc hcent L L' d d' h h'
    letI := ftrParaOf hT hS hc hcent L L' d d' h h'
    letI := ftrTopOf hT hS hc hcent L L'' d d'' h h''
    letI := ftrT2Of hT hS hc hcent L L'' d d'' h h''
    letI := ftrParaOf hT hS hc hcent L L'' d d'' h h''
    MPolyfold.IsScSmoothOnFibredProduct (ftrMOf hT hS hc hcent L' L'' d' d'' h' h'')
      (ftrMOf hT hS hc hcent L L' d d' h h') (ftrMOf hT hS hc hcent L L'' d d'' h h'')
      (ftrSrcOf hT hS hc hcent L' L'' d' d'' h' h'')
      (ftrTgtOf hT hS hc hcent L L' d d' h h').isScSmoothMap GroupoidStr.TransitionSet.mul
  | _, _, _, d, d', d'', rfl, rfl, rfl =>
    d.V.ftr_isScSmoothMap_mul hT hS d'.V d''.V d.hθ d'.hθ d''.hθ

variable (hT hS) in
/-- **The polyfold structure `(F_bC, M)` on `bC`** (2021 Theorem 17.4.26, p. 809): `F_bC(ᾱ)`
consists of the face uniformizers `Ψ_θ` at `ᾱ`, and `M(Ψ_θ, Ψ'_{θ'})` carries the natural
M-polyfold structure of Definition 17.4.14 (Theorem 17.4.16 for the structure maps). -/
def bdryConstruction : (S.bdryGCT hT hS hc hcent).PolyfoldConstruction where
  F := S.bdryF hT hS hc hcent
  isAt ᾱ L hL := by
    obtain ⟨d, -, he, rfl⟩ := hL
    exact ⟨⟨d.o, d.V.mem_of_mem_faces d.hθ⟩, he⟩
  topM L L' := ftrTopOf hT hS hc hcent L.1 L'.1 (faceDataOf hc hcent L) (faceDataOf hc hcent L')
    (faceDataOf_eq hc hcent L) (faceDataOf_eq hc hcent L')
  t2M L L' := ftrT2Of hT hS hc hcent L.1 L'.1 (faceDataOf hc hcent L) (faceDataOf hc hcent L')
    (faceDataOf_eq hc hcent L) (faceDataOf_eq hc hcent L')
  paraM L L' := ftrParaOf hT hS hc hcent L.1 L'.1 (faceDataOf hc hcent L)
    (faceDataOf hc hcent L') (faceDataOf_eq hc hcent L) (faceDataOf_eq hc hcent L')
  M L L' := ftrMOf hT hS hc hcent L.1 L'.1 (faceDataOf hc hcent L) (faceDataOf hc hcent L')
    (faceDataOf_eq hc hcent L) (faceDataOf_eq hc hcent L')
  isLocalScDiffeo_src L L' := ftrSrcOf hT hS hc hcent L.1 L'.1 (faceDataOf hc hcent L)
    (faceDataOf hc hcent L') (faceDataOf_eq hc hcent L) (faceDataOf_eq hc hcent L')
  isLocalScDiffeo_tgt L L' := ftrTgtOf hT hS hc hcent L.1 L'.1 (faceDataOf hc hcent L)
    (faceDataOf hc hcent L') (faceDataOf_eq hc hcent L) (faceDataOf_eq hc hcent L')
  isScSmoothMap_unit L := ftrUnitOf hT hS hc hcent L.1 (faceDataOf hc hcent L)
    (faceDataOf_eq hc hcent L)
  isScSmoothMap_inv L L' := ftrInvOf hT hS hc hcent L.1 L'.1 (faceDataOf hc hcent L)
    (faceDataOf hc hcent L') (faceDataOf_eq hc hcent L) (faceDataOf_eq hc hcent L')
  isScSmoothMap_mul L L' L'' := ftrMulOf hT hS hc hcent L.1 L'.1 L''.1 (faceDataOf hc hcent L)
    (faceDataOf hc hcent L') (faceDataOf hc hcent L'') (faceDataOf_eq hc hcent L)
    (faceDataOf_eq hc hcent L') (faceDataOf_eq hc hcent L'')

variable (hT hS) in
/-- (17.74) for `L = Ψ_θ`, `L' = Ψ'_{θ'}`: `M(L, L') ≃ M(Ψ, Ψ')*_{θ,θ'}`. -/
def ftrInclOf : ∀ (L L' : (S.bdryGCT hT hS hc hcent).LocalUniformizer) (d d' : S.FaceData),
    L = d.unif hT hS hc hcent → L' = d'.unif hT hS hc hcent →
    L.Trans L' → d.V.transFaceSet hT d'.V d.hθ d'.hθ
  | _, _, d, d', rfl, rfl => d.V.ftrHomeomorph hT hS d'.V d.hθ d'.hθ

variable (hT hS) in
theorem ftrInclOf_spec : ∀ (L L' : (S.bdryGCT hT hS hc hcent).LocalUniformizer)
    (d d' : S.FaceData) (h : L = d.unif hT hS hc hcent) (h' : L' = d'.unif hT hS hc hcent),
    letI := ftrTopOf hT hS hc hcent L L' d d' h h'
    letI := ftrT2Of hT hS hc hcent L L' d d' h h'
    letI := ftrParaOf hT hS hc hcent L L' d d' h h'
    Bijective (ftrInclOf hT hS hc hcent L L' d d' h h') ∧
      (ftrMOf hT hS hc hcent L L' d d' h h').IsLocalScDiffeo
        (MPolyfold.subPolyfold (d.V.isSubMPolyfold_transFaceSet d'.V d.hθ d'.hθ))
        (ftrInclOf hT hS hc hcent L L' d d' h h') ∧
      ∀ a : L.Trans L', (ftrInclOf hT hS hc hcent L L' d d' h h' a).1.mor = a.mor.mor ∧
        d.Ψ.1.obj (ftrInclOf hT hS hc hcent L L' d d' h h' a).1.src = (L.obj a.src).α ∧
        d'.Ψ.1.obj (ftrInclOf hT hS hc hcent L L' d d' h h' a).1.tgt = (L'.obj a.tgt).α
  | _, _, d, d', rfl, rfl =>
    ⟨(d.V.ftrHomeomorph hT hS d'.V d.hθ d'.hθ).bijective,
      d.V.ftr_isLocalScDiffeo_homeomorph hT hS d'.V d.hθ d'.hθ,
      fun _ => ⟨rfl, (d.V.faceObj_α _ _ _).symm, (d'.V.faceObj_α _ _ _).symm⟩⟩

theorem hasUniformizers_bdryConstruction :
    (S.bdryConstruction hT hS hc hcent).HasUniformizers := by
  intro a
  obtain ⟨t, rfl⟩ := BdryTuple.toBObj_surjective (S := S) (hT := hT) (hS := hS) a
  let d : S.FaceData := ⟨t.unif, t.o, t.V, hcent.fixesPoint t.mem t.obj_o, t.θ, t.face⟩
  have he : d.V.faceObj hT hS d.hθ d.o (d.V.mem_of_mem_faces d.hθ) = t.toBObj hT hS := by
    rw [GoodNbhd.faceObj_center, BdryTuple.toBObj_eq_ptObj]
  have hm : d.Ψ.1 ∈ S.F (t.toBObj hT hS).α := t.mem
  exact ⟨d.unif hT hS hc hcent, d, hm, he, rfl⟩


variable (hT hS) in
/-- **2021 Theorem 17.4.26, p. 809**: for a tame polyfold `(C, F, M)` with `F(α) ≠ ∅` for all
`α`, `Ĉ`-continuous and centred uniformizers, the tame boundary `bC` (a GCT with the metrizable
topology `T_bC`, Theorem 17.4.19) carries the polyfold structure `(F_bC, M)`:
* every object of `bC` has a uniformizer in `F_bC`;
* `F_bC(ᾱ)` consists of the face uniformizers `Ψ_θ : G_θ ⋉ θ → bC` (Lemma 17.4.6) built from
  `Ψ ∈ F(α)`, a good open neighbourhood `U(ō)` and a face `θ` of `U(ō)` with `Ψ_θ(ō) = ᾱ`;
* for `L = Ψ_θ`, `L' = Ψ'_{θ'}` the transition M-polyfold `M(L, L')` is identified by (17.74)
  with the sub-M-polyfold `M(Ψ, Ψ')*_{θ,θ'}` of `M(Ψ, Ψ')` (Lemma 17.4.13): the identification is
  a bijection and a local sc-diffeomorphism onto the sub-M-polyfold, hence sc-smooth into
  `M(Ψ, Ψ')`, and it keeps the underlying morphism and the objects. -/
theorem theorem_17_4_26 :
    (S.bdryConstruction hT hS hc hcent).HasUniformizers ∧
    (∀ ᾱ L, L ∈ (S.bdryConstruction hT hS hc hcent).F ᾱ ↔ ∃ d : S.FaceData,
      d.Ψ.1 ∈ S.F ᾱ.α ∧ d.V.faceObj hT hS d.hθ d.o (d.V.mem_of_mem_faces d.hθ) = ᾱ ∧
        L = d.unif hT hS hc hcent) ∧
    ∀ L L' : (S.bdryConstruction hT hS hc hcent).Unif,
      L.1 = (faceDataOf hc hcent L).unif hT hS hc hcent ∧
      ∃ ι : (S.bdryConstruction hT hS hc hcent).Tr L L' →
          (faceDataOf hc hcent L).V.transFaceSet hT (faceDataOf hc hcent L').V
            (faceDataOf hc hcent L).hθ (faceDataOf hc hcent L').hθ,
        Bijective ι ∧
        ((S.bdryConstruction hT hS hc hcent).transPolyfold L L').IsLocalScDiffeo
          (MPolyfold.subPolyfold ((faceDataOf hc hcent L).V.isSubMPolyfold_transFaceSet
            (faceDataOf hc hcent L').V (faceDataOf hc hcent L).hθ (faceDataOf hc hcent L').hθ))
          ι ∧
        ((S.bdryConstruction hT hS hc hcent).transPolyfold L L').IsScSmoothMap
          (S.transPolyfold (faceDataOf hc hcent L).Ψ (faceDataOf hc hcent L').Ψ)
          (fun a => (ι a).1) ∧
        ∀ a : (S.bdryConstruction hT hS hc hcent).Tr L L',
          (ι a).1.mor = a.mor.mor ∧
          (faceDataOf hc hcent L).Ψ.1.obj (ι a).1.src = (L.1.obj a.src).α ∧
          (faceDataOf hc hcent L').Ψ.1.obj (ι a).1.tgt = (L'.1.obj a.tgt).α := by
  refine ⟨hasUniformizers_bdryConstruction hc hcent, fun _ _ => Iff.rfl,
    fun L L' => ⟨faceDataOf_eq hc hcent L, ?_⟩⟩
  obtain ⟨hb, hl, hm⟩ := ftrInclOf_spec hT hS hc hcent L.1 L'.1 (faceDataOf hc hcent L)
    (faceDataOf hc hcent L') (faceDataOf_eq hc hcent L) (faceDataOf_eq hc hcent L')
  let ι : (S.bdryConstruction hT hS hc hcent).Tr L L' → _ := ftrInclOf hT hS hc hcent L.1 L'.1
    (faceDataOf hc hcent L) (faceDataOf hc hcent L') (faceDataOf_eq hc hcent L)
    (faceDataOf_eq hc hcent L')
  have hl' : ((S.bdryConstruction hT hS hc hcent).transPolyfold L L').IsLocalScDiffeo
      (MPolyfold.subPolyfold ((faceDataOf hc hcent L).V.isSubMPolyfold_transFaceSet
        (faceDataOf hc hcent L').V (faceDataOf hc hcent L).hθ (faceDataOf hc hcent L').hθ))
      ι := hl
  exact ⟨ι, hb, hl', (MPolyfold.subPolyfold_inclusion_isScSmooth _).comp hl'.isScSmoothMap, hm⟩


end Construction

end GCT.PolyfoldConstruction

end Polyfold

namespace Polyfold.GCT.PolyfoldConstruction.GoodNbhd

open TameBoundary

variable {C : GCT.{u}} {S : C.PolyfoldConstruction} {hT : S.IsTame} {hS : S.HasUniformizers}
variable {Ψ Ψ' : S.Unif} {o : Ψ.1.O} {o' : Ψ'.1.O} (V : S.GoodNbhd Ψ o) (V' : S.GoodNbhd Ψ' o')

variable (hT hS) in
/-- **2021 (17.84), p. 811**: the map `M(Ψ_θ, Ψ'_{θ'}) → M(Ψ, Ψ')`, `(x, Φ, x') ↦ (x, φ, x')`,
is an sc-smooth local embedding: injective, a local sc-diffeomorphism onto the sub-M-polyfold
`M(Ψ, Ψ')*_{θ,θ'}` (whose image it is), sc-smooth into `M(Ψ, Ψ')`, and compatible with the
structure maps `s`, `t` and with the forgetful functor `B` (`Φ ↦ φ`). -/
theorem display_17_84 {θ : Set Ψ.1.O} {θ' : Set Ψ'.1.O} (hθ : θ ∈ V.faces)
    (hθ' : θ' ∈ V'.faces) :
    Injective (fun h : V.FTr hT hS V' hθ hθ' => V.faceTrToTr V' h) ∧
    range (fun h : V.FTr hT hS V' hθ hθ' => V.faceTrToTr V' h) = V.transFaceSet hT V' hθ hθ' ∧
    (V.ftrPolyfold hT hS V' hθ hθ').IsLocalScDiffeo
      (MPolyfold.subPolyfold (V.isSubMPolyfold_transFaceSet V' hθ hθ'))
      (V.ftrHomeomorph hT hS V' hθ hθ') ∧
    (V.ftrPolyfold hT hS V' hθ hθ').IsScSmoothMap (S.transPolyfold Ψ Ψ')
      (fun h : V.FTr hT hS V' hθ hθ' => V.faceTrToTr V' h) ∧
    ∀ h : V.FTr hT hS V' hθ hθ', (V.faceTrToTr V' h).src = h.src.1 ∧
      (V.faceTrToTr V' h).tgt = h.tgt.1 ∧ (V.faceTrToTr V' h).mor = h.mor.mor := by
  refine ⟨V.faceTrToTr_injective V' hθ hθ', ?_, V.ftr_isLocalScDiffeo_homeomorph hT hS V' hθ hθ',
    (MPolyfold.subPolyfold_inclusion_isScSmooth _).comp
      (V.ftr_isLocalScDiffeo_homeomorph hT hS V' hθ hθ').isScSmoothMap,
    fun _ => ⟨rfl, rfl, rfl⟩⟩
  ext a
  constructor
  · rintro ⟨h, rfl⟩
    exact (V.ftrHomeomorph hT hS V' hθ hθ' h).2
  · intro ha
    exact ⟨(V.ftrHomeomorph hT hS V' hθ hθ').symm ⟨a, ha⟩,
      congrArg Subtype.val ((V.ftrHomeomorph hT hS V' hθ hθ').apply_symm_apply ⟨a, ha⟩)⟩

variable (hT hS) in
/-- **2021 (17.82), p. 810**: the functor `F : Θ → G ⋉ O` with `B ∘ Ψ̂ = Ψ ∘ F`. On objects
`(x, θ) ↦ x` is sc-smooth (the inclusion `θ → O` of the sub-M-polyfold `θ`) and
`B(Ψ_θ(x)) = Ψ(x)`; on morphisms `M(Ψ_θ, Ψ_{θ'}) → M(Ψ, Ψ)`, `(x, Φ, x') ↦ (x, φ, x')`, is
sc-smooth and compatible with `s`, `t` and `B` ((17.84) with `Ψ' = Ψ`). -/
theorem display_17_82 {θ θ' : Set Ψ.1.O} (hθ : θ ∈ V.faces) (hθ' : θ' ∈ V.faces) :
    (V.faceSubPolyfold hT hθ).IsScSmoothMap Ψ.1.P (Subtype.val : θ → Ψ.1.O) ∧
    (∀ x (hx : x ∈ θ), (V.faceObj hT hS hθ x hx).α = Ψ.1.obj x) ∧
    (V.ftrPolyfold hT hS V hθ hθ').IsScSmoothMap (S.transPolyfold Ψ Ψ)
      (fun h : V.FTr hT hS V hθ hθ' => V.faceTrToTr V h) ∧
    ∀ h : V.FTr hT hS V hθ hθ', (V.faceTrToTr V h).src = h.src.1 ∧
      (V.faceTrToTr V h).tgt = h.tgt.1 ∧ (V.faceTrToTr V h).mor = h.mor.mor :=
  ⟨MPolyfold.subPolyfold_inclusion_isScSmooth _, fun x hx => V.faceObj_α hθ x hx,
    (V.display_17_84 hT hS V hθ hθ').2.2.2.1, (V.display_17_84 hT hS V hθ hθ').2.2.2.2⟩

variable (hT hS) in
/-- **2021 (17.83), p. 811**: with `V(ō)` in place of `O`, the objects of `Θ` cover
`U(ō) = V(ō) ∩ ∂O` (`⋃ θ = U(ō)`), and `|B|⁻¹(|Ψ(V(ō))|) = ⋃_θ |Ψ_θ(θ)| = |Ψ̂(Θ)|`. -/
theorem display_17_83 (hc : S.HatContinuous) (hfix : Ψ.1.FixesPoint o) :
    ⋃₀ V.faces = V.bdry ∧
    S.bdrySigma hT hS ⁻¹' ((fun q : Ψ.1.O => C.toGroupoidStr.π (Ψ.1.obj q)) '' V.1.U) =
      ⋃ (θ : Set Ψ.1.O) (hθ : θ ∈ V.faces), V.faceImage hT hS hθ := by
  refine ⟨V.sUnion_faces, Subset.antisymm (fun z hz => ?_) ?_⟩
  · obtain ⟨θ, hθ, hz⟩ := V.exists_mem_faceImage hc hfix hz
    exact mem_iUnion₂.2 ⟨θ, hθ, hz⟩
  · refine iUnion₂_subset fun θ hθ => ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, (V.subset_bdry hθ hx).1, by rw [bdrySigma_π, GoodNbhd.faceObj_α]⟩

end Polyfold.GCT.PolyfoldConstruction.GoodNbhd

namespace Polyfold

open TameBoundary

namespace GCT.PolyfoldConstruction

section SwapWitness

open MPolyfold TameBoundaryExample EpGroupoid.Examples

variable (W : ScBanach)

/-- The slice `[0,∞)² ⊕ W` with the group `ℤ/2`. -/
def swapSlice₀ : TranslationSlice ℤˣ (quadrant 2 W 0) where
  V := univ
  isOpen := isOpen_univ
  nonempty := ⟨⟨0, zero_mem_quadrant 2 W⟩, mem_univ _⟩
  H := ⊤
  smul_mem _ _ _ _ := mem_univ _
  mem_of_smul_mem k _ _ _ := Subgroup.mem_top k

theorem coord_neg_one_smul (i : Fin 2) (p : quadrant 2 W 0) :
    coord i ((-1 : ℤˣ) • p) = coord (Equiv.swap (0 : Fin 2) 1 i) p := by
  rw [neg_one_smul_eq]; rfl

/-- The slice `{p₁ < p₀}` with the trivial group. -/
def swapSliceLt (i j : Fin 2) (hij : Equiv.swap (0 : Fin 2) 1 i = j) :
    TranslationSlice ℤˣ (quadrant 2 W 0) where
  V := {p | coord i p < coord j p}
  isOpen := isOpen_lt (TameBoundaryExample.continuous_coord i)
    (TameBoundaryExample.continuous_coord j)
  nonempty := by
    refine ⟨⟨((fun k => if k = j then 1 else 0 : Fin 2 → ℝ), 0), fun k => by
      change (0 : ℝ) ≤ if k = j then 1 else 0
      split_ifs <;> norm_num⟩, ?_⟩
    have hne : i ≠ j := by
      rintro rfl; revert hij; revert i; decide
    change (if i = j then (1 : ℝ) else 0) < if j = j then 1 else 0
    rw [if_neg hne, if_pos rfl]; norm_num
  H := ⊥
  smul_mem h hh v hv := by
    rw [Subgroup.mem_bot.1 hh, one_smul]; exact hv
  mem_of_smul_mem k v hv hkv := by
    rcases Int.units_eq_one_or k with rfl | rfl
    · exact Subgroup.one_mem _
    · exfalso
      have h1 : coord i ((-1 : ℤˣ) • v) < coord j ((-1 : ℤˣ) • v) := hkv
      have hji : Equiv.swap (0 : Fin 2) 1 j = i := by rw [← hij, Equiv.swap_apply_self]
      rw [coord_neg_one_smul, coord_neg_one_smul, hij, hji] at h1
      exact lt_asymm h1 hv

theorem mem_swapSliceLt {i j : Fin 2} {hij : Equiv.swap (0 : Fin 2) 1 i = j} {p : quadrant 2 W 0} :
    p ∈ (swapSliceLt W i j hij).V ↔ coord i p < coord j p := Iff.rfl

/-- The point with `p_j = 1`, the other coordinate `0`, and `w = 0`. -/
def swapPt (j : Fin 2) : quadrant 2 W 0 :=
  ⟨((fun k => if k = j then 1 else 0 : Fin 2 → ℝ), 0), fun k => by
    change (0 : ℝ) ≤ if k = j then 1 else 0
    split_ifs <;> norm_num⟩

theorem coord_swapPt (i j : Fin 2) : coord i (swapPt W j) = if i = j then 1 else 0 := rfl

/-- The three slices: `[0,∞)² ⊕ W` (group `ℤ/2`), `{p₀ < p₁}` and `{p₁ < p₀}` (trivial group). -/
def swapSlices : Set (TranslationSlice ℤˣ (quadrant 2 W 0)) :=
  {swapSlice₀ W, swapSliceLt W 0 1 (Equiv.swap_apply_left 0 1),
    swapSliceLt W 1 0 (Equiv.swap_apply_right 0 1)}

theorem swapSlices_overlapping : Overlapping (swapSlices W) := by
  have h0 : ∀ D ∈ swapSlices W, ∃ v ∈ D.V, ∃ k : ℤˣ, k • v ∈ (swapSlice₀ W).V :=
    fun D _ => ⟨D.nonempty.some, D.nonempty.some_mem, 1, mem_univ _⟩
  have hpt : ∀ D ∈ swapSlices W, ∀ j : Fin 2, ∃ v ∈ D.V, ∃ k : ℤˣ,
      k • v = swapPt W j := by
    intro D hD j
    rcases hD with rfl | rfl | rfl
    · exact ⟨swapPt W j, mem_univ _, 1, one_smul _ _⟩
    · refine ⟨swapPt W 1, ?_, ?_⟩
      · rw [mem_swapSliceLt, coord_swapPt, coord_swapPt]; norm_num
      · fin_cases j
        · refine ⟨-1, Subtype.ext (Prod.ext (funext fun i => ?_) rfl)⟩
          change coord i ((-1 : ℤˣ) • swapPt W 1) = coord i (swapPt W 0)
          rw [coord_neg_one_smul, coord_swapPt, coord_swapPt]
          fin_cases i <;> simp
        · exact ⟨1, one_smul _ _⟩
    · refine ⟨swapPt W 0, ?_, ?_⟩
      · rw [mem_swapSliceLt, coord_swapPt, coord_swapPt]; norm_num
      · fin_cases j
        · exact ⟨1, one_smul _ _⟩
        · refine ⟨-1, Subtype.ext (Prod.ext (funext fun i => ?_) rfl)⟩
          change coord i ((-1 : ℤˣ) • swapPt W 0) = coord i (swapPt W 1)
          rw [coord_neg_one_smul, coord_swapPt, coord_swapPt]
          fin_cases i <;> simp
  intro D hD D' hD'
  rcases hD' with rfl | rfl | rfl
  · exact h0 D hD
  · obtain ⟨v, hv, k, hk⟩ := hpt D hD 1
    refine ⟨v, hv, k, ?_⟩
    rw [hk, mem_swapSliceLt, coord_swapPt, coord_swapPt]; norm_num
  · obtain ⟨v, hv, k, hk⟩ := hpt D hD 0
    refine ⟨v, hv, k, ?_⟩
    rw [hk, mem_swapSliceLt, coord_swapPt, coord_swapPt]; norm_num

/-- `F(x)`: the slice uniformizers `Ψ_D`, `x ∈ V_D`, whose group `H_D` fixes `x`. -/
def swapF (x : quadrant 2 W 0) :
    Set (GCT.translation ℤˣ (quadrant 2 W 0) (isScSmoothMap_swap_smul W)).LocalUniformizer :=
  {L | ∃ D ∈ swapSlices W, x ∈ D.V ∧ (∀ h ∈ D.H, h • x = x) ∧
    L = D.unif (quadrantPolyfold 2 W) (isScSmoothMap_swap_smul W)}

theorem swapF_subset (x : quadrant 2 W 0) :
    swapF W x ⊆ sliceF (quadrantPolyfold 2 W) (isScSmoothMap_swap_smul W) (swapSlices W) x :=
  fun _ ⟨D, hD, hx, _, h⟩ => ⟨D, hD, hx, h⟩

/-- **The swap polyfold `ℤ/2 ⋉ ([0,∞)² ⊕ W)`**, `−1` exchanging the two coordinates: `F(x)`
consists of the inclusion of `[0,∞)² ⊕ W` with the group `ℤ/2` if `x` lies on the diagonal
`p₀ = p₁`, and of the inclusion of `{p₀ < p₁}` or `{p₁ < p₀}` with the trivial group otherwise. -/
abbrev swapConstruction :
    (GCT.translation ℤˣ (quadrant 2 W 0) (isScSmoothMap_swap_smul W)).PolyfoldConstruction :=
  (sliceConstruction (quadrantPolyfold 2 W) (isScSmoothMap_swap_smul W) (swapSlices W)
    (swapSlices_overlapping W)).restrictF (swapF W) (swapF_subset W)

theorem swapConstruction_isTame : (swapConstruction W).IsTame := fun α L hL =>
  sliceConstruction_isTame _ _ (swapSlices_overlapping W) (quadrantPolyfold_isTame 2 W) α L
    (swapF_subset W α hL)

theorem swapQ_eq_self {x : quadrant 2 W 0} (h : coord 0 x = coord 1 x) : swapQ W x = x := by
  refine Subtype.ext (Prod.ext (funext fun i => ?_) rfl)
  change coord i (swapQ W x) = coord i x
  rw [coord_swapQ]
  fin_cases i
  · exact h.symm
  · exact h

theorem swapConstruction_hasUniformizers : (swapConstruction W).HasUniformizers := by
  intro x
  rcases lt_trichotomy (coord 0 x) (coord 1 x) with h | h | h
  · refine ⟨_, swapSliceLt W 0 1 (Equiv.swap_apply_left 0 1), Or.inr (Or.inl rfl), h,
      fun k hk => by rw [Subgroup.mem_bot.1 hk, one_smul], rfl⟩
  · refine ⟨_, swapSlice₀ W, Or.inl rfl, mem_univ _, fun k _ => ?_, rfl⟩
    rcases Int.units_eq_one_or k with rfl | rfl
    · exact one_smul _ _
    · rw [neg_one_smul_eq]; exact swapQ_eq_self W h
  · refine ⟨_, swapSliceLt W 1 0 (Equiv.swap_apply_right 0 1), Or.inr (Or.inr rfl), h,
      fun k hk => by rw [Subgroup.mem_bot.1 hk, one_smul], rfl⟩

theorem swapConstruction_hatContinuous : (swapConstruction W).HatContinuous := fun Ψ =>
  sliceConstruction_continuous_hat (unifOfSubset _ (swapF_subset W) Ψ)

theorem swapConstruction_isCentred : (swapConstruction W).IsCentred := by
  rintro x L ⟨D, -, hx, hfix, rfl⟩
  exact ⟨⟨x, hx⟩, rfl, fun g => Subtype.ext (hfix g.1 g.2)⟩

theorem swapQ_corner : swapQ W (corner W) = corner W := swapQ_eq_self W rfl

/-- The uniformizer `Ψ₀ : ℤ/2 ⋉ ([0,∞)² ⊕ W) → C` at the corner `0`. -/
abbrev swapUnif₀ : (swapConstruction W).Unif :=
  ⟨(swapSlice₀ W).unif (quadrantPolyfold 2 W) (isScSmoothMap_swap_smul W), corner W, swapSlice₀ W,
    Or.inl rfl, mem_univ _, fun k _ => by
      rcases Int.units_eq_one_or k with rfl | rfl
      · exact one_smul _ _
      · rw [neg_one_smul_eq]; exact swapQ_corner W, rfl⟩

/-- The corner as a point of the domain of `Ψ₀`. -/
abbrev swapCorner : (swapUnif₀ W).1.O := ⟨corner W, mem_univ _⟩

/-- The element `−1` of the group `ℤ/2` of `Ψ₀`. -/
abbrev swapGen : (swapUnif₀ W).1.G := ⟨-1, Subgroup.mem_top _⟩

/-- The point `(0, 1)` as a point of the domain of `Ψ₀`. -/
abbrev swapPt₀ : (swapUnif₀ W).1.O := ⟨swapPt W 0, mem_univ _⟩

theorem degIndex_swapUnif₀ (y : (swapUnif₀ W).1.O) :
    (swapUnif₀ W).1.P.degIndex y = dq 2 W y.1 := by
  have := (swapSlice₀ W).paracompactSpace (quadrantPolyfold 2 W)
  exact MPolyfold.degIndex_restrictOpen (quadrantPolyfold 2 W) (swapSlice₀ W).isOpen y

/-- Every face of an open subset of the domain of `Ψ₀` lies in a coordinate face `{p_k = 0}`
and meets the stratum `part k`. -/
theorem exists_part_of_isFaceIn {U θ : Set (swapUnif₀ W).1.O}
    (hθ : IsFaceIn (swapUnif₀ W).1.P.degIndex U θ) :
    ∃ k : Fin 2, ∃ p ∈ θ, p.1 ∈ part k ∧ ∀ y ∈ θ, coord k y.1 = 0 := by
  obtain ⟨p, hpU, hp1, rfl⟩ := hθ
  have hp1' : dq 2 W p.1 = 1 := by rw [← degIndex_swapUnif₀]; exact hp1
  obtain ⟨k, hk⟩ := dq_eq_one_iff.1 hp1'
  have hA : Subtype.val '' connectedComponentIn (U ∩ {y | (swapUnif₀ W).1.P.degIndex y = 1}) p ⊆
      part k := by
    refine subset_part (isPreconnected_connectedComponentIn.image _
      continuous_subtype_val.continuousOn) ?_ (mem_image_of_mem _ (mem_connectedComponentIn
        ⟨hpU, hp1⟩)) hk
    rintro _ ⟨y, hy, rfl⟩
    have := (connectedComponentIn_subset _ _ hy).2
    change (swapUnif₀ W).1.P.degIndex y = 1 at this
    exact (degIndex_swapUnif₀ W y).symm.trans this
  refine ⟨k, p, mem_faceAt_self hpU hp1, hk, fun y hy => ?_⟩
  have hy' : y.1 ∈ closure (part k) :=
    closure_mono hA (image_closure_subset_closure_image continuous_subtype_val ⟨y, hy.2, rfl⟩)
  exact closure_minimal (fun q hq => hq.1)
    (isClosed_eq (TameBoundaryExample.continuous_coord k) continuous_const) hy'

/-- `−1` moves every face of an open subset of the domain of `Ψ₀`. -/
theorem swapGen_smul_ne {U θ : Set (swapUnif₀ W).1.O}
    (hθ : IsFaceIn (swapUnif₀ W).1.P.degIndex U θ) : swapGen W • θ ≠ θ := by
  intro he
  obtain ⟨k, p, hp, hpk, hθk⟩ := exists_part_of_isFaceIn W hθ
  have hgp : swapGen W • p ∈ θ := he ▸ Set.smul_mem_smul_set hp
  have h0 := hθk _ hgp
  change coord k ((-1 : ℤˣ) • p.1) = 0 at h0
  rw [coord_neg_one_smul] at h0
  have hne : Equiv.swap (0 : Fin 2) 1 k ≠ k := by fin_cases k <;> decide
  exact (hpk.2 _ hne).ne' h0

/-- **The non-degenerate witness with a non-trivial group** for §17.4 (Lemma 17.4.6, Lemma
17.4.8, Theorem 17.4.19, Theorem 17.4.26): the swap polyfold `ℤ/2 ⋉ ([0,∞)² ⊕ W)` is tame, has
uniformizers, `Ψ̂` is continuous and every uniformizer is centred; the uniformizer
`Ψ₀ ∈ F(0)` at the corner has the group `ℤ/2`, whose element `−1` acts non-trivially; a good
neighbourhood `U(0)` has two faces, `−1` exchanges them (so each face stabiliser `G_θ` is
trivial), and the two face uniformizers have the same image `|Ψ_θ(θ)| = |Ψ_{θ'}(θ')|` in `|bC|`. -/
theorem swap_tameBoundary_witness :
    ∃ (hT : (swapConstruction W).IsTame) (hS : (swapConstruction W).HasUniformizers),
      (swapConstruction W).HatContinuous ∧ (swapConstruction W).IsCentred ∧
      (swapUnif₀ W).1 ∈ (swapConstruction W).F (corner W) ∧
      (swapUnif₀ W).1.obj (swapCorner W) = corner W ∧
      (swapUnif₀ W).1.FixesPoint (swapCorner W) ∧
      swapGen W • swapPt₀ W ≠ swapPt₀ W ∧
      ∃ V : (swapConstruction W).GoodNbhd (swapUnif₀ W) (swapCorner W),
        V.faces.encard = 2 ∧ (∀ θ ∈ V.faces, swapGen W • θ ∈ V.faces ∧ swapGen W • θ ≠ θ) ∧
        ∃ (θ θ' : Set (swapUnif₀ W).1.O) (hθ : θ ∈ V.faces) (hθ' : θ' ∈ V.faces),
          θ ≠ θ' ∧ V.faceImage hT hS hθ = V.faceImage hT hS hθ' := by
  have hT := swapConstruction_isTame W
  have hS := swapConstruction_hasUniformizers W
  have hc := swapConstruction_hatContinuous W
  have hcent := swapConstruction_isCentred W
  have hmem : (swapUnif₀ W).1 ∈ (swapConstruction W).F (corner W) :=
    ⟨swapSlice₀ W, Or.inl rfl, mem_univ _, fun k _ => by
      rcases Int.units_eq_one_or k with rfl | rfl
      · exact one_smul _ _
      · rw [neg_one_smul_eq]; exact swapQ_corner W, rfl⟩
  have hfix : (swapUnif₀ W).1.FixesPoint (swapCorner W) := hcent.fixesPoint hmem rfl
  have hd : (swapUnif₀ W).1.P.degIndex (swapCorner W) = 2 := by
    rw [degIndex_swapUnif₀]; exact quadrantPolyfold_degIndex_zero 2 W
  have hb : swapCorner W ∈ (swapUnif₀ W).1.P.boundary := by
    change 1 ≤ _
    rw [hd]; decide
  obtain ⟨V, -⟩ := (swapConstruction W).exists_goodNbhd (Ψ := swapUnif₀ W)
    (isTame_unif _ hT _) hb isOpen_univ (mem_univ _)
  have hV2 : V.faces.encard = 2 := by rw [V.encard_faces, hd]; rfl
  have hmove : ∀ θ ∈ V.faces, swapGen W • θ ∈ V.faces ∧ swapGen W • θ ≠ θ := fun θ hθ =>
    ⟨V.smul_mem_faces hfix (swapGen W) hθ, swapGen_smul_ne W (V.mem_faces_iff.1 hθ)⟩
  obtain ⟨θ, hθ⟩ : V.faces.Nonempty := by
    rw [← Set.encard_pos, hV2]; norm_num
  refine ⟨hT, hS, hc, hcent, hmem, rfl, hfix, ?_, V, hV2, hmove, θ, _, hθ, (hmove θ hθ).1,
    (hmove θ hθ).2.symm, (V.lemma_17_4_8 hc hfix hθ (hmove θ hθ).1).2.2 ⟨_, rfl⟩⟩
  intro h
  have h1 := congrArg (fun y : (swapUnif₀ W).1.O => coord 0 y.1) h
  change coord 0 ((-1 : ℤˣ) • swapPt W 0) = coord 0 (swapPt W 0) at h1
  rw [coord_neg_one_smul, coord_swapPt, coord_swapPt] at h1
  norm_num at h1

/-- **Theorem 17.4.26 for the swap polyfold**: its tame boundary carries the polyfold structure
`(F_bC, M)`, with a uniformizer at every object. -/
theorem swap_theorem_17_4_26 :
    ∃ (hT : (swapConstruction W).IsTame) (hS : (swapConstruction W).HasUniformizers)
      (hc : (swapConstruction W).HatContinuous) (hcent : (swapConstruction W).IsCentred),
      ((swapConstruction W).bdryConstruction hT hS hc hcent).HasUniformizers :=
  ⟨swapConstruction_isTame W, swapConstruction_hasUniformizers W,
    swapConstruction_hatContinuous W, swapConstruction_isCentred W,
    hasUniformizers_bdryConstruction _ _⟩

end SwapWitness

end GCT.PolyfoldConstruction

end Polyfold
