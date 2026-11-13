import Polyfold.Chapter11.EpEquivalenceGeometry
import Polyfold.Chapter7.TameBoundaryEp
import Polyfold.Chapter7.NonVacuity
import Polyfold.Chapter2.TameBoundaryExample
import Polyfold.Chapter2.TameSub

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 11, §11.1 "Ep-Groupoids and Equivalences" (pp. 523–526; 2017: pp. 377–380):
**Definition 11.1.3** (2017: Definition 11.1), **Example 11.1.4** (2017: Example 11.1),
**Remark 11.1.5** (2017: Remark 11.1), **Proposition 11.1.6** (2017: Proposition 11.2),
**Remark 11.1.7** (2017: Remark 11.2) and **Proposition 11.1.8** (2017: Proposition 11.3).
Numbers and pages are the 2021 text's, the 2017 ones in parentheses.

# Faces of tame ep-groupoids up to equivalence

## The text, paraphrased

(p. 523) Faces of a tame M-polyfold are closures of connected components of `{d_X = 1}`
(Definition 2.5.10); for an ep-groupoid and `θ ⊆ |X|`, `X_θ` is the full subcategory on the
objects `x` with `|x| ∈ θ`.  (Definition 11.1.3) For a tame ep-groupoid `X`, a face (in the
ep-groupoid sense) is `X_θ` for `θ` the closure in `|X|` of a connected component of
`{z ∈ |X| | d_{|X|}(z) = 1}` (`θ` a face of `|X|`); `X` is face structured if every `z ∈ |X|` lies
in exactly `d_{|X|}(z)` faces of `|X|`, weakly face structured if the object M-polyfold is face
structured.  (Example 11.1.4) `C = [0, ∞)²` with only identities is face structured; `ℤ/2 ⋉ C`,
`−1` exchanging the coordinates, is weakly face structured but not face structured.
(Remark 11.1.5, p. 524) Ordered face structures (no statement); by [56, Proposition 3.15] an
equivalence `Φ` gives bijections `Φ_*(F) = saturation(Φ(F))`, `Φ^*(G) = Φ⁻¹(G)` of the faces,
`Φ^* = (Φ_*)⁻¹`, and face structured passes along `Φ`; a generalized isomorphism
`[X ←Φ A →Ψ Y]` gives `[d]_* = Ψ_* ∘ Φ^*`, `[d]^* = Φ_* ∘ Ψ^*`, mutually inverse.
(Proposition 11.1.6) For `X` face structured: each face has a sub-M-polyfold object set with
tame induced structure, likewise the morphisms, and is an ep-groupoid; a nonempty intersection of
two faces is a face of each; a generalized isomorphism `[d]` induces `[d]_*` and generalized
isomorphisms `[d]_F : F → [d]_*(F)` ((11.1): the restrictions of `Φ`, `Ψ`).  *Proof*: `|[d]|` is
a homeomorphism preserving `d_{|·|}`, so `[d]_*(X_θ) = Y_{|[d]|(θ)}`.  (Remark 11.1.7, p. 525) If
`X ≅ Y` in `EP(E⁻¹)` and one is tame and face structured, so is the other.  (Proposition 11.1.8,
p. 526) If `|f| = |g|` for generalized isomorphisms of tame face-structured ep-groupoids, then
`f_* = g_*` and the induced maps `|F| → |f_*F|` agree.

## What is formalized

* **Definition 11.1.3**: `EpGroupoid.IsOrbitFace` (faces of `|X|`), `faceObj`, `faceMor` (the full
  subcategory `X_θ`; `faceMor_eq`, `isSaturated_faceObj`), `IsEpFace`, `orbitFacesThrough`,
  `IsEpFaceStructured`, `IsWeaklyFaceStructured`; `isOrbitFace_iff_isFaceIn`,
  `isEpFaceStructured_iff` (comparison with Chapter 2's `TameBoundary.IsFaceIn`).
* Transport along a homeomorphism preserving the index: `isDHomeoOn_univ`,
  `isFaceIn_univ_image`, `exists_isFaceIn_univ_preimage`, `isFaceStructuredOpen_univ_iff`.
* `EpFunctor.IsEquivalence.isTame_of_isTame_left` (tameness passes forward along an equivalence;
  with Chapter 10's `isTame_of_isTame`, both ways), `isTame_iff`.
* **Remark 11.1.5**: `EpFunctor.saturation_image_faceObj` (`Φ_*(X_θ) = Y_{|Φ|(θ)}`),
  `EpFunctor.preimage_faceObj` (`Φ^*(Y_θ') = X_{|Φ|⁻¹(θ')}`), `EpFunctor.IsEquivalence.bijOn_faces`;
  `EPLoc.faceMap`, `EPLoc.faceComap` (`[d]_*`, `[d]^*` on faces of `|X|`), `faceMap_homMk`,
  `faceComap_homMk` (`[d]_* = Ψ_* ∘ Φ^*`, `[d]^* = Φ_* ∘ Ψ^*`); `EPLoc.remark_11_1_5`.
* **Proposition 11.1.6**, the part on `[d]_*`: `EPLoc.proposition_11_1_6` (bijection of faces,
  inverse `[d]^*`, `[d]_*(X_θ) = Y_{|[d]|(θ)}`, `|[d]|` a homeomorphism `θ → [d]_*θ`).
* **Remark 11.1.7**: `EPLoc.remark_11_1_7`.  **Proposition 11.1.8**: `EPLoc.proposition_11_1_8`.
* **Example 11.1.4**: `Examples.example_11_1_4` for `C = [0, ∞)² ⊕ W` (`W = 0` is the text's
  case): `trivial C` is face structured; `ℤ/2 ⋉ C` (`swapEpGroupoid`) is weakly face structured
  and not face structured (`{d_{|X|} = 1}` is connected, so `|0|` lies in one face only).

## What the text leaves implicit, and the choices made

* A face `X_θ` is recorded by its object set `π⁻¹(θ)` and morphism set `s⁻¹(π⁻¹(θ))`; here
  `[d]_F` appears through its orbit map, the restriction of `|[d]|` (`proposition_11_1_6`,
  `proposition_11_1_8`).  The ep-groupoid structure on it (Proposition 11.1.6) and `[d]_F` are
  built in `FaceEpGroupoids.lean` (`faceEpGroupoid`, `proposition_11_1_6_faces`) and
  `FaceGeneralizedIso.lean` (`EPLoc.faceIso`, `proposition_11_1_6_faceIso`,
  `proposition_11_1_8_faceIso`); the intersection clause is settled in `FaceIntersectionCounterexample.lean`
  (it does not hold as we read it) and `FaceIntersectionUnion.lean` (the union form).
* Faces of `|X|` are those of Chapter 2 for the index `d_{|X|}` on the open set `|X|`, so the
  transport lemmas of Chapter 7's `TameBoundary.IsDHomeoOn` apply.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

open TameBoundary

universe u v

/-! ### Transport of faces along index-preserving homeomorphisms -/

namespace TameBoundary

variable {S : Type u} [TopologicalSpace S] {T : Type v} [TopologicalSpace T] {dS : S → ℕ}
  {dT : T → ℕ} {e : S → T}

/-- A homeomorphism preserving the index is an index-preserving homeomorphism on `univ`. -/
theorem isDHomeoOn_univ (he : IsHomeomorph e) (hd : ∀ s, dT (e s) = dS s) :
    IsDHomeoOn dS dT e univ :=
  ⟨isOpen_univ, he.continuous.continuousOn, he.injective.injOn,
    fun U hU _ => he.isOpenMap U hU, fun s _ => hd s⟩

theorem isFaceIn_univ_image (he : IsHomeomorph e) (hd : ∀ s, dT (e s) = dS s) {θ : Set S}
    (hθ : IsFaceIn dS univ θ) : IsFaceIn dT univ (e '' θ) := by
  have h := (isDHomeoOn_univ he hd).isFaceIn_image subset_rfl hθ
  rwa [image_univ_of_surjective he.surjective] at h

theorem exists_isFaceIn_univ_preimage (he : IsHomeomorph e) (hd : ∀ s, dT (e s) = dS s)
    {θ' : Set T} (hθ' : IsFaceIn dT univ θ') : IsFaceIn dS univ (e ⁻¹' θ') := by
  rw [← image_univ_of_surjective he.surjective] at hθ'
  obtain ⟨θ, hθ, rfl⟩ := (isDHomeoOn_univ he hd).exists_isFaceIn_of_image subset_rfl hθ'
  rwa [he.injective.preimage_image]

theorem isFaceStructuredOpen_univ_iff (he : IsHomeomorph e) (hd : ∀ s, dT (e s) = dS s) :
    IsFaceStructuredOpen dS univ ↔ IsFaceStructuredOpen dT univ := by
  refine ⟨fun h => ?_, fun h => ⟨isOpen_univ, fun y _ => ?_⟩⟩
  · have h' := (isDHomeoOn_univ he hd).isFaceStructuredOpen_image subset_rfl h
    rwa [image_univ_of_surjective he.surjective] at h'
  · have h' := (isDHomeoOn_univ he hd).encard_facesThrough_image subset_rfl (mem_univ y)
    rw [image_univ_of_surjective he.surjective, h.2 _ (mem_univ _), hd] at h'
    exact h'.symm

end TameBoundary

/-! ### Definition 11.1.3 -/

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- **2021 Definition 11.1.3, p. 523 (2017: Definition 11.1, p. 377)**: `θ ⊆ |X|` is a **face of
`|X|`** if it is the closure in `|X|` of a connected component of `{z ∈ |X| | d_{|X|}(z) = 1}`. -/
def IsOrbitFace (θ : Set X.OrbitSpace) : Prop :=
  ∃ z, X.degIndexOrbit z = 1 ∧
    θ = closure (connectedComponentIn {w | X.degIndexOrbit w = 1} z)

/-- The object set `{x ∈ X | |x| ∈ θ}` of the full subcategory `X_θ` (2021 p. 523). -/
def faceObj (θ : Set X.OrbitSpace) : Set Obj := X.π ⁻¹' θ

/-- The morphism set of the full subcategory `X_θ`: the morphisms between objects of `X_θ`. -/
def faceMor (θ : Set X.OrbitSpace) : Set Mor :=
  {φ | X.src φ ∈ X.faceObj θ ∧ X.tgt φ ∈ X.faceObj θ}

/-- **Definition 11.1.3**: a **face of `X`** (in the ep-groupoid sense) is the full subcategory
`X_θ` of a face `θ` of `|X|`, recorded by its object set. -/
def IsEpFace (A : Set Obj) : Prop := ∃ θ, X.IsOrbitFace θ ∧ A = X.faceObj θ

/-- The faces of `|X|` containing `z`. -/
def orbitFacesThrough (z : X.OrbitSpace) : Set (Set X.OrbitSpace) :=
  {θ | X.IsOrbitFace θ ∧ z ∈ θ}

/-- **Definition 11.1.3**: the tame ep-groupoid `X` is **face structured** (in the ep-groupoid
sense) if every `z ∈ |X|` lies in exactly `d_{|X|}(z)` faces of `|X|`. -/
def IsEpFaceStructured : Prop :=
  X.IsTame ∧ ∀ z, (X.orbitFacesThrough z).encard = X.degIndexOrbit z

/-- **Definition 11.1.3**: the tame ep-groupoid `X` is **weakly face structured** if the object
M-polyfold is face structured (Definition 2.5.10). -/
def IsWeaklyFaceStructured : Prop := X.IsTame ∧ X.PObj.IsFaceStructured

variable {X}

/-- A morphism of `X_θ` is a morphism with source in `X_θ` (`X_θ` is saturated). -/
theorem faceMor_eq (θ : Set X.OrbitSpace) : X.faceMor θ = X.src ⁻¹' X.faceObj θ := by
  ext φ
  refine ⟨And.left, fun h => ⟨h, ?_⟩⟩
  change X.π (X.tgt φ) ∈ θ
  rw [← X.π_src_eq_π_tgt φ]
  exact h

theorem isSaturated_faceObj (θ : Set X.OrbitSpace) : X.IsSaturated (X.faceObj θ) := by
  change X.π ⁻¹' (X.π '' (X.π ⁻¹' θ)) = X.π ⁻¹' θ
  rw [image_preimage_eq θ X.surjective_π]

theorem isOrbitFace_iff_isFaceIn {θ : Set X.OrbitSpace} :
    X.IsOrbitFace θ ↔ IsFaceIn X.degIndexOrbit univ θ := by
  simp only [IsFaceIn, faceAt, IsOrbitFace, univ_inter, mem_univ, true_and]

theorem orbitFacesThrough_eq (z : X.OrbitSpace) :
    X.orbitFacesThrough z = facesThrough X.degIndexOrbit univ z := by
  ext θ
  exact and_congr_left' isOrbitFace_iff_isFaceIn

theorem isEpFaceStructured_iff :
    X.IsEpFaceStructured ↔ X.IsTame ∧ IsFaceStructuredOpen X.degIndexOrbit univ := by
  simp only [IsEpFaceStructured, IsFaceStructuredOpen, orbitFacesThrough_eq, isOpen_univ,
    mem_univ, true_and, forall_const]

end EpGroupoid

/-! ### Tameness along equivalences -/

namespace EpFunctor.IsEquivalence

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {F : EpFunctor X Y}

open WeakFibredProduct in
/-- If `F : X → Y` is an equivalence and `X` is tame, so is `Y`: in `X ×_Y Y` (for `F` and `1_Y`)
`πX` is an equivalence, so `X ×_Y Y` is tame, and `πY` is a surjective local sc-diffeomorphism
on objects (essential surjectivity of `F`). -/
theorem isTame_of_isTame_left (hF : F.IsEquivalence) (hX : X.IsTame) : Y.IsTame := by
  have h : Admissible F (EpFunctor.id Y) := .of_isEquivalence_right (EpFunctor.IsEquivalence.id Y)
  have hW : (epGroupoid F (EpFunctor.id Y) h).IsTame :=
    (isEquivalence_projLeft (EpFunctor.IsEquivalence.id Y) h).isTame_of_isTame hX
  have hsurj : Surjective (projRight F (EpFunctor.id Y) h).obj := fun y => by
    obtain ⟨x, ψ, hs, ht⟩ := hF.exists_iso y
    exact ⟨WeakFibredProduct.Obj.mk F (EpFunctor.id Y) x ψ y hs ht, rfl⟩
  exact ((isEquivalence_projRight hF h).isLocalScDiffeo_obj.isTame_iff_of_surjective hsurj).1 hW

theorem isTame_iff (hF : F.IsEquivalence) : X.IsTame ↔ Y.IsTame :=
  ⟨hF.isTame_of_isTame_left, hF.isTame_of_isTame⟩

/-- `|F|` preserves the induced degeneracy index. -/
theorem degIndexOrbit_orbitMap (hF : F.IsEquivalence) (q : X.OrbitSpace) :
    Y.degIndexOrbit (F.orbitMap q) = X.degIndexOrbit q := by
  obtain ⟨x, rfl⟩ := X.surjective_π q
  rw [GroupoidFunctor.orbitMap_π, EpGroupoid.degIndexOrbit_π, EpGroupoid.degIndexOrbit_π,
    hF.degIndex_obj]

end EpFunctor.IsEquivalence

/-! ### Remark 11.1.5: the bijections `Φ_*`, `Φ^*` of an equivalence -/

namespace EpFunctor

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}

/-- **`Φ_*(X_θ) = saturation(Φ(X_θ)) = Y_{|Φ|(θ)}`** (Remark 11.1.5). -/
theorem saturation_image_faceObj (Φ : EpFunctor X Y) (θ : Set X.OrbitSpace) :
    Y.saturation (Φ.obj '' X.faceObj θ) = Y.faceObj (Φ.orbitMap '' θ) := by
  change Y.π ⁻¹' (Y.π '' (Φ.obj '' (X.π ⁻¹' θ))) = Y.π ⁻¹' (Φ.orbitMap '' θ)
  congr 1
  rw [image_image]
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨X.π x, hx, GroupoidFunctor.orbitMap_π _ x⟩
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨x, rfl⟩ := X.surjective_π q
    exact ⟨x, hq, (GroupoidFunctor.orbitMap_π _ x).symm⟩

/-- **`Φ^*(Y_θ') = Φ⁻¹(Y_θ') = X_{|Φ|⁻¹(θ')}`** (Remark 11.1.5). -/
theorem preimage_faceObj (Φ : EpFunctor X Y) (θ' : Set Y.OrbitSpace) :
    Φ.obj ⁻¹' Y.faceObj θ' = X.faceObj (Φ.orbitMap ⁻¹' θ') := by
  ext x
  change Y.π (Φ.obj x) ∈ θ' ↔ Φ.orbitMap (X.π x) ∈ θ'
  rw [GroupoidFunctor.orbitMap_π]

/-- An equivalence `Φ` induces the bijection `θ ↦ |Φ|(θ)` of the faces of `|X|` onto those of
`|Y|`, with inverse `θ' ↦ |Φ|⁻¹(θ')` (Remark 11.1.5, [56, Proposition 3.15]). -/
theorem IsEquivalence.bijOn_faces {Φ : EpFunctor X Y} (hΦ : Φ.IsEquivalence) :
    BijOn (image Φ.orbitMap) {θ | X.IsOrbitFace θ} {θ' | Y.IsOrbitFace θ'} ∧
      InvOn (preimage Φ.orbitMap) (image Φ.orbitMap) {θ | X.IsOrbitFace θ}
        {θ' | Y.IsOrbitFace θ'} ∧
      MapsTo (preimage Φ.orbitMap) {θ' | Y.IsOrbitFace θ'} {θ | X.IsOrbitFace θ} := by
  have he := hΦ.isHomeomorph_orbitMap
  have hd := hΦ.degIndexOrbit_orbitMap
  have h₁ : MapsTo (image Φ.orbitMap) {θ | X.IsOrbitFace θ} {θ' | Y.IsOrbitFace θ'} :=
    fun θ hθ => EpGroupoid.isOrbitFace_iff_isFaceIn.2
      (isFaceIn_univ_image he hd (EpGroupoid.isOrbitFace_iff_isFaceIn.1 hθ))
  have h₂ : MapsTo (preimage Φ.orbitMap) {θ' | Y.IsOrbitFace θ'} {θ | X.IsOrbitFace θ} :=
    fun θ' hθ' => EpGroupoid.isOrbitFace_iff_isFaceIn.2
      (exists_isFaceIn_univ_preimage he hd (EpGroupoid.isOrbitFace_iff_isFaceIn.1 hθ'))
  have h₃ : InvOn (preimage Φ.orbitMap) (image Φ.orbitMap) {θ | X.IsOrbitFace θ}
      {θ' | Y.IsOrbitFace θ'} :=
    ⟨fun θ _ => he.injective.preimage_image θ, fun θ' _ => he.surjective.image_preimage θ'⟩
  exact ⟨h₃.bijOn h₁ h₂, h₃, h₂⟩

end EpFunctor

/-! ### Generalized isomorphisms: `[d]_*` and `[d]^*` -/

namespace EPLocalization

namespace EPLoc

variable {X Y : EP.{u}}

/-- `|[d]|` is a homeomorphism for a generalized isomorphism. -/
theorem isHomeomorph_orbitMap {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) :
    IsHomeomorph (orbitMap f) := by
  obtain ⟨d, rfl, hΦ⟩ := exists_diagram_of_isGeneralizedIso hf
  exact d.isHomeomorph_orbitMap hΦ

/-- **`[d]_*`** on faces of `|X|` (Remark 11.1.5): `θ ↦ |[d]|(θ)`; on full subcategories
`X_θ ↦ Y_{|[d]|(θ)}`. -/
def faceMap (f : of X ⟶ of Y) (θ : Set X.X.OrbitSpace) : Set Y.X.OrbitSpace := orbitMap f '' θ

/-- **`[d]^*`** on faces of `|Y|` (Remark 11.1.5): `θ' ↦ |[d]|⁻¹(θ')`. -/
def faceComap (f : of X ⟶ of Y) (θ' : Set Y.X.OrbitSpace) : Set X.X.OrbitSpace :=
  orbitMap f ⁻¹' θ'

/-- **`[d]_* = Ψ_* ∘ Φ^*`** for a representative `X ←Φ A →Ψ Y` (Remark 11.1.5). -/
theorem faceMap_homMk (d : Diagram X Y) (θ : Set X.X.OrbitSpace) :
    faceMap (homMk d) θ = d.Φ.orbitMap '' (d.F.orbitMap ⁻¹' θ) := by
  rw [faceMap, orbitMap_homMk]
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨r, rfl⟩ := d.isEquivalence_F.isHomeomorph_orbitMap.surjective p
    exact ⟨r, hp, (d.orbitMap_orbitMap_F r).symm⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨_, hr, d.orbitMap_orbitMap_F r⟩

/-- **`[d]^* = Φ_* ∘ Ψ^*`** for a representative `X ←Φ A →Ψ Y` (Remark 11.1.5). -/
theorem faceComap_homMk (d : Diagram X Y) (θ' : Set Y.X.OrbitSpace) :
    faceComap (homMk d) θ' = d.F.orbitMap '' (d.Φ.orbitMap ⁻¹' θ') := by
  rw [faceComap, orbitMap_homMk]
  ext p
  obtain ⟨r, rfl⟩ := d.isEquivalence_F.isHomeomorph_orbitMap.surjective p
  simp only [mem_preimage, d.orbitMap_orbitMap_F,
    d.isEquivalence_F.isHomeomorph_orbitMap.injective.mem_set_image]

variable {f : of X ⟶ of Y} (hf : IsGeneralizedIso f)
include hf

theorem isOrbitFace_faceMap {θ : Set X.X.OrbitSpace} (hθ : X.X.IsOrbitFace θ) :
    Y.X.IsOrbitFace (faceMap f θ) :=
  EpGroupoid.isOrbitFace_iff_isFaceIn.2 (isFaceIn_univ_image (isHomeomorph_orbitMap hf)
    (degIndexOrbit_orbitMap hf) (EpGroupoid.isOrbitFace_iff_isFaceIn.1 hθ))

theorem isOrbitFace_faceComap {θ' : Set Y.X.OrbitSpace} (hθ' : Y.X.IsOrbitFace θ') :
    X.X.IsOrbitFace (faceComap f θ') :=
  EpGroupoid.isOrbitFace_iff_isFaceIn.2 (exists_isFaceIn_univ_preimage (isHomeomorph_orbitMap hf)
    (degIndexOrbit_orbitMap hf) (EpGroupoid.isOrbitFace_iff_isFaceIn.1 hθ'))

theorem faceComap_faceMap (θ : Set X.X.OrbitSpace) : faceComap f (faceMap f θ) = θ :=
  (isHomeomorph_orbitMap hf).injective.preimage_image θ

theorem faceMap_faceComap (θ' : Set Y.X.OrbitSpace) : faceMap f (faceComap f θ') = θ' :=
  (isHomeomorph_orbitMap hf).surjective.image_preimage θ'

/-- `[d]_*` and `[d]^*` are mutually inverse bijections of the faces of `|X|` and `|Y|`. -/
theorem bijOn_faceMap :
    BijOn (faceMap f) {θ | X.X.IsOrbitFace θ} {θ' | Y.X.IsOrbitFace θ'} ∧
      InvOn (faceComap f) (faceMap f) {θ | X.X.IsOrbitFace θ} {θ' | Y.X.IsOrbitFace θ'} := by
  have h₃ : InvOn (faceComap f) (faceMap f) {θ | X.X.IsOrbitFace θ} {θ' | Y.X.IsOrbitFace θ'} :=
    ⟨fun θ _ => faceComap_faceMap hf θ, fun θ' _ => faceMap_faceComap hf θ'⟩
  exact ⟨h₃.bijOn (fun θ hθ => isOrbitFace_faceMap hf hθ)
    (fun θ' hθ' => isOrbitFace_faceComap hf hθ'), h₃⟩

omit hf in
/-- **2021 Remark 11.1.5, p. 524 (2017: Remark 11.1, p. 378)**, the bijections: for an
equivalence `Φ`, `θ ↦ |Φ|(θ)` is a bijection of the faces of `|X|` onto those of `|Y|`, with
`Φ_*(X_θ) = saturation(Φ(X_θ)) = Y_{|Φ|(θ)}` and `Φ^*(Y_θ') = Φ⁻¹(Y_θ') = X_{|Φ|⁻¹(θ')}`; for a
generalized isomorphism `[d] = [X ←Φ A →Ψ Y]`, `[d]_* = Ψ_* ∘ Φ^*`, `[d]^* = Φ_* ∘ Ψ^*`, and they
are mutually inverse bijections. -/
theorem remark_11_1_5 :
    (∀ {A B : EP.{u}} (Φ : EpFunctor A.X B.X), Φ.IsEquivalence →
      BijOn (image Φ.orbitMap) {θ | A.X.IsOrbitFace θ} {θ' | B.X.IsOrbitFace θ'} ∧
        (∀ θ, B.X.saturation (Φ.obj '' A.X.faceObj θ) = B.X.faceObj (Φ.orbitMap '' θ)) ∧
        ∀ θ', Φ.obj ⁻¹' B.X.faceObj θ' = A.X.faceObj (Φ.orbitMap ⁻¹' θ')) ∧
      (∀ (d : Diagram X Y), d.Φ.IsEquivalence →
        (∀ θ, faceMap (homMk d) θ = d.Φ.orbitMap '' (d.F.orbitMap ⁻¹' θ)) ∧
        (∀ θ', faceComap (homMk d) θ' = d.F.orbitMap '' (d.Φ.orbitMap ⁻¹' θ')) ∧
        BijOn (faceMap (homMk d)) {θ | X.X.IsOrbitFace θ} {θ' | Y.X.IsOrbitFace θ'} ∧
        InvOn (faceComap (homMk d)) (faceMap (homMk d)) {θ | X.X.IsOrbitFace θ}
          {θ' | Y.X.IsOrbitFace θ'}) :=
  ⟨fun Φ hΦ => ⟨hΦ.bijOn_faces.1, Φ.saturation_image_faceObj, Φ.preimage_faceObj⟩,
    fun d hΦ => ⟨faceMap_homMk d, faceComap_homMk d,
      bijOn_faceMap ((theorem_10_3_10 d).1.2 hΦ)⟩⟩

/-- **2021 Proposition 11.1.6, p. 524 (2017: Proposition 11.2, p. 378)**, the part on `[d]_*`:
a generalized isomorphism `[d] : X → Y` induces the bijection `[d]_*` of the faces of `|X|` onto
those of `|Y|`, with inverse `[d]^*`; `[d]_*(X_θ) = Y_{|[d]|(θ)}`; and the map of orbit spaces
`|[d]_F| : θ → [d]_*θ` of the restriction to a face is a homeomorphism (the restriction of
`|[d]|`).  The ep-groupoid structure of a face and the intersection statement are not
formalized. -/
theorem proposition_11_1_6 :
    BijOn (faceMap f) {θ | X.X.IsOrbitFace θ} {θ' | Y.X.IsOrbitFace θ'} ∧
      InvOn (faceComap f) (faceMap f) {θ | X.X.IsOrbitFace θ} {θ' | Y.X.IsOrbitFace θ'} ∧
      (∀ θ, Y.X.faceObj (faceMap f θ) = Y.X.π ⁻¹' (orbitMap f '' θ)) ∧
      ∀ θ : Set X.X.OrbitSpace, MapsTo (orbitMap f) θ (faceMap f θ) ∧
        IsHomeomorph ((isHomeomorph_orbitMap hf).homeomorph.image θ) :=
  ⟨(bijOn_faceMap hf).1, (bijOn_faceMap hf).2, fun _ => rfl,
    fun θ => ⟨mapsTo_image _ θ, Homeomorph.isHomeomorph _⟩⟩

/-- **2021 Remark 11.1.7, p. 525 (2017: Remark 11.2, p. 379)**: if `f : X → Y` is a generalized
isomorphism, `X` is tame and face structured iff `Y` is. -/
theorem remark_11_1_7 : X.X.IsEpFaceStructured ↔ Y.X.IsEpFaceStructured := by
  have hT : X.X.IsTame ↔ Y.X.IsTame :=
    iff_of_isGeneralizedIso (fun A => A.X.IsTame) (fun _ hF => hF.isTame_iff) hf
  rw [EpGroupoid.isEpFaceStructured_iff, EpGroupoid.isEpFaceStructured_iff, hT,
    isFaceStructuredOpen_univ_iff (isHomeomorph_orbitMap hf) (degIndexOrbit_orbitMap hf)]

omit hf in
/-- **2021 Proposition 11.1.8, p. 526 (2017: Proposition 11.3, p. 380)**: for generalized
isomorphisms `f, g : X → Y` of tame face-structured ep-groupoids with `|f| = |g|`, `f_* = g_*`,
and the maps `|F| → |f_* F|` induced on the faces (the restrictions of `|f|`, `|g|`) agree. -/
theorem proposition_11_1_8 {f g : of X ⟶ of Y} (_hf : IsGeneralizedIso f)
    (_hg : IsGeneralizedIso g) (_hX : X.X.IsEpFaceStructured) (_hY : Y.X.IsEpFaceStructured)
    (h : orbitMap f = orbitMap g) :
    faceMap f = faceMap g ∧ faceComap f = faceComap g ∧
      ∀ θ : Set X.X.OrbitSpace, MapsTo (orbitMap f) θ (faceMap g θ) ∧
        EqOn (orbitMap f) (orbitMap g) θ := by
  refine ⟨?_, ?_, fun θ => ⟨?_, fun q _ => congrFun h q⟩⟩
  · funext θ; rw [faceMap, faceMap, h]
  · funext θ; rw [faceComap, faceComap, h]
  · rw [faceMap, ← h]; exact mapsTo_image _ θ

end EPLoc

end EPLocalization

/-! ### Example 11.1.4 -/

namespace EpGroupoid.Examples

open MPolyfold TameBoundaryExample TameSubExample

variable (W : ScBanach)

/-- The exchange of the two coordinates of `ℝ²`. -/
def swapCLM : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  LinearMap.toContinuousLinearMap (LinearMap.funLeft ℝ ℝ (Equiv.swap (0 : Fin 2) 1))

/-- The sc-operator `(a, w) ↦ (a ∘ swap, w)` of `ℝ² ⊕ W`. -/
def swapOp : ScOperator ((ScBanach.const (Fin 2 → ℝ)).prod W) ((ScBanach.const (Fin 2 → ℝ)).prod W)
    where
  lvl m := swapCLM.prodMap (ContinuousLinearMap.id ℝ (W m))
  incl_comm _ _ := rfl

theorem swapOp_mem (p : ((ScBanach.const (Fin 2 → ℝ)).prod W) 0) (hp : p ∈ quadrant 2 W 0) :
    swapOp W 0 p ∈ quadrant 2 W 0 := fun _ => hp _

/-- The exchange of the coordinates of `C = [0, ∞)² ⊕ W`. -/
def swapQ (p : quadrant 2 W 0) : quadrant 2 W 0 := ⟨swapOp W 0 p.1, swapOp_mem W p.1 p.2⟩

theorem coord_swapQ (i : Fin 2) (p : quadrant 2 W 0) :
    coord i (swapQ W p) = coord (Equiv.swap (0 : Fin 2) 1 i) p := rfl

theorem swapQ_swapQ (p : quadrant 2 W 0) : swapQ W (swapQ W p) = p := by
  refine Subtype.ext (Prod.ext (funext fun i => ?_) rfl)
  change p.1.1 (Equiv.swap (0 : Fin 2) 1 (Equiv.swap (0 : Fin 2) 1 i)) = p.1.1 i
  rw [Equiv.swap_apply_self]

/-- `ℤ/2 = ℤˣ = {±1}` acting on `C`, `−1` exchanging the coordinates. -/
instance instMulActionSwap : MulAction ℤˣ (quadrant 2 W 0) where
  smul k p := if k = 1 then p else swapQ W p
  one_smul _ := if_pos rfl
  mul_smul a b p := by
    change (if a * b = 1 then p else swapQ W p) =
      if a = 1 then (if b = 1 then p else swapQ W p) else swapQ W (if b = 1 then p else swapQ W p)
    rcases Int.units_eq_one_or a with rfl | rfl <;> rcases Int.units_eq_one_or b with rfl | rfl <;>
      simp [swapQ_swapQ]

theorem neg_one_smul_eq (p : quadrant 2 W 0) : (-1 : ℤˣ) • p = swapQ W p :=
  if_neg (by decide)

theorem isScSmoothMap_swap_smul (k : ℤˣ) :
    (quadrantPolyfold 2 W).IsScSmoothMap (quadrantPolyfold 2 W) fun y => k • y := by
  rcases Int.units_eq_one_or k with rfl | rfl
  · simp only [one_smul]
    exact MPolyfold.isScSmoothMap_id
  · have h : (fun y : quadrant 2 W 0 => (-1 : ℤˣ) • y) = swapQ W := funext (neg_one_smul_eq W)
    rw [h]
    exact quadrantMap_isScSmoothMap (swapOp W) (swapOp_mem W)

/-- **`ℤ/2 ⋉ C`** (Example 11.1.4), `C = [0, ∞)² ⊕ W`, `−1` exchanging the coordinates. -/
def swapEpGroupoid : EpGroupoid (quadrant 2 W 0) (ℤˣ × quadrant 2 W 0) :=
  actionEpGroupoid (isScSmoothMap_swap_smul W)

/-- The corner `0 ∈ C`. -/
def corner : quadrant 2 W 0 := ⟨0, zero_mem_quadrant 2 W⟩

/-- The points `((0, t), 0)` of the stratum `part 0` of `C`, `t > 0`. -/
def edgePt (t : ℝ) (w : W 0) : quadrant 2 W 0 :=
  ⟨((![0, max t 0] : Fin 2 → ℝ), w), fun i => by
    fin_cases i
    · exact le_rfl
    · exact le_max_right t 0⟩

theorem continuous_edgePt : Continuous fun q : ℝ × W 0 => edgePt W q.1 q.2 := by
  refine Continuous.subtype_mk (Continuous.prodMk ?_ continuous_snd) _
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact continuous_const
  · exact (continuous_fst.max continuous_const)

theorem edgePt_mem_part {t : ℝ} (ht : 0 < t) (w : W 0) : edgePt W t w ∈ part (0 : Fin 2) := by
  refine ⟨rfl, fun l hl => ?_⟩
  fin_cases l
  · exact absurd rfl hl
  · change 0 < max t 0
    exact lt_max_of_lt_left ht

theorem part_zero_eq : part (0 : Fin 2) = (fun q : ℝ × W 0 => edgePt W q.1 q.2) ''
    (Ioi 0 ×ˢ univ) := by
  ext p
  constructor
  · rintro ⟨h0, h1⟩
    have h1' : 0 < coord 1 p := h1 1 (by decide)
    refine ⟨(coord 1 p, p.1.2), ⟨h1', mem_univ _⟩, Subtype.ext (Prod.ext (funext fun i => ?_) rfl)⟩
    fin_cases i
    · exact h0.symm
    · exact max_eq_left h1'.le
  · rintro ⟨q, ⟨hq, -⟩, rfl⟩
    exact edgePt_mem_part W hq q.2

theorem isConnected_part_zero : IsConnected (part (0 : Fin 2) : Set (quadrant 2 W 0)) := by
  rw [part_zero_eq]
  exact (isConnected_Ioi.prod isConnected_univ).image _ (continuous_edgePt W).continuousOn

theorem edgePt_zero : edgePt W 0 0 = corner W :=
  Subtype.ext (Prod.ext (funext fun i => by fin_cases i <;> simp [edgePt, corner]) rfl)

theorem corner_mem_closure_part : corner W ∈ closure (part (0 : Fin 2) : Set (quadrant 2 W 0)) := by
  rw [← edgePt_zero]
  have hc : Continuous fun t : ℝ => edgePt W t 0 :=
    (continuous_edgePt W).comp (continuous_id.prodMk continuous_const)
  refine mem_closure_of_tendsto (b := 𝓝[>] (0 : ℝ))
    (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact edgePt_mem_part W ht 0

theorem degIndexOrbit_swap (p : quadrant 2 W 0) :
    (swapEpGroupoid W).degIndexOrbit ((swapEpGroupoid W).π p) = dq 2 W p := rfl

/-- In `|ℤ/2 ⋉ C|`, `{d_{|X|} = 1}` is the image of the connected stratum `part 0`. -/
theorem setOf_degIndexOrbit_eq_one_swap :
    {z | (swapEpGroupoid W).degIndexOrbit z = 1} = (swapEpGroupoid W).π '' part (0 : Fin 2) := by
  ext z
  obtain ⟨p, rfl⟩ := (swapEpGroupoid W).surjective_π z
  rw [Set.mem_ofPred_eq, degIndexOrbit_swap, dq_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    fin_cases k
    · exact ⟨p, hk, rfl⟩
    · refine ⟨swapQ W p, ⟨hk.1, fun l hl => ?_⟩, ?_⟩
      · fin_cases l
        · exact absurd rfl hl
        · exact hk.2 0 (by decide)
      · rw [← neg_one_smul_eq]
        exact ((action_π_eq_π_iff (isScSmoothMap_swap_smul W)).2 ⟨-1, rfl⟩).symm
  · rintro ⟨q, hq, hqp⟩
    obtain ⟨k, rfl⟩ := (action_π_eq_π_iff (isScSmoothMap_swap_smul W)).1 hqp
    rcases Int.units_eq_one_or k with rfl | rfl
    · exact ⟨0, by rwa [one_smul]⟩
    · refine ⟨1, ?_⟩
      rw [neg_one_smul_eq]
      refine ⟨hq.1, fun l hl => ?_⟩
      fin_cases l
      · exact hq.2 1 (by decide)
      · exact absurd rfl hl

/-- `ℤ/2 ⋉ C` has exactly one face of `|X|`, the closure of `{d_{|X|} = 1}`. -/
theorem isOrbitFace_swap_iff (θ : Set (swapEpGroupoid W).OrbitSpace) :
    (swapEpGroupoid W).IsOrbitFace θ ↔
      θ = closure {z | (swapEpGroupoid W).degIndexOrbit z = 1} := by
  have hS : IsConnected {z | (swapEpGroupoid W).degIndexOrbit z = 1} := by
    rw [setOf_degIndexOrbit_eq_one_swap]
    exact (isConnected_part_zero W).image _ (swapEpGroupoid W).continuous_π.continuousOn
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [hS.isPreconnected.connectedComponentIn hz]
  · rintro rfl
    obtain ⟨z, hz⟩ := hS.nonempty
    exact ⟨z, hz, by rw [hS.isPreconnected.connectedComponentIn hz]⟩

theorem not_isEpFaceStructured_swap : ¬ (swapEpGroupoid W).IsEpFaceStructured := by
  rintro ⟨-, h⟩
  have hc := h ((swapEpGroupoid W).π (corner W))
  have hfaces : (swapEpGroupoid W).orbitFacesThrough ((swapEpGroupoid W).π (corner W)) =
      {closure {z | (swapEpGroupoid W).degIndexOrbit z = 1}} := by
    ext θ
    refine ⟨fun hθ => (isOrbitFace_swap_iff W θ).1 hθ.1, fun hθ => ⟨(isOrbitFace_swap_iff W θ).2 hθ,
      ?_⟩⟩
    rw [mem_singleton_iff.1 hθ, setOf_degIndexOrbit_eq_one_swap]
    exact closure_mono (image_mono subset_rfl) <|
      (map_mem_closure (swapEpGroupoid W).continuous_π (corner_mem_closure_part W)
        fun x hx => mem_image_of_mem _ hx)
  rw [hfaces, encard_singleton, degIndexOrbit_swap] at hc
  have h2 : dq 2 W (corner W) = 2 := quadrantPolyfold_degIndex_zero 2 W
  rw [h2] at hc
  exact absurd hc (by decide)

/-- `C` is a face-structured tame M-polyfold. -/
theorem isFaceStructured_quadrant (n : ℕ) : (quadrantPolyfold n W).IsFaceStructured := by
  intro x
  have h := (isFaceStructuredOpen_quadrant (W := W) (n := n) isOpen_univ).2 x (mem_univ x)
  rw [← h]
  congr 1
  ext θ
  exact and_congr_left' ((quadrantPolyfold n W).isFaceIn_univ_iff).symm

/-- For the trivial ep-groupoid, `π : Z → |Z|` is a homeomorphism. -/
theorem isHomeomorph_π_trivial {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]
    (P : MPolyfold Z) : IsHomeomorph (trivial P).π := by
  refine ⟨(trivial P).continuous_π, (trivial P).proposition_7_1_8, fun x y hxy => ?_,
    (trivial P).surjective_π⟩
  obtain ⟨φ, rfl, rfl⟩ := (trivial P).π_eq_π_iff.1 hxy
  rfl

/-- **2021 Example 11.1.4, p. 523 (2017: Example 11.1, p. 377)**, for `C = [0, ∞)² ⊕ W` (the text
has `W = 0`): (1) `C` with only identities is a face structured ep-groupoid; (2) `ℤ/2 ⋉ C`, `−1`
exchanging the coordinates, is weakly face structured and not face structured. -/
theorem example_11_1_4 :
    (trivial (quadrantPolyfold 2 W)).IsEpFaceStructured ∧
      (swapEpGroupoid W).IsWeaklyFaceStructured ∧ ¬ (swapEpGroupoid W).IsEpFaceStructured := by
  refine ⟨?_, ⟨quadrantPolyfold_isTame 2 W, isFaceStructured_quadrant W 2⟩,
    not_isEpFaceStructured_swap W⟩
  refine EpGroupoid.isEpFaceStructured_iff.2 ⟨quadrantPolyfold_isTame 2 W, ?_⟩
  exact (isFaceStructuredOpen_univ_iff (isHomeomorph_π_trivial _)
    fun _ => rfl).1 (isFaceStructuredOpen_quadrant isOpen_univ)

end EpGroupoid.Examples

end Polyfold
