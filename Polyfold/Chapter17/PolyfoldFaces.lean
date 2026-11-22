import Polyfold.Chapter17.Subpolyfold
import Polyfold.Chapter17.PolyfoldLevels
import Polyfold.Chapter11.FaceEpGroupoids

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.3 (pp. 786–787): **Definition 17.3.7** (faces of a tame polyfold, face-structured) and
**Proposition 17.3.8** (faces are subpolyfolds).  Numbers and pages are the 2021 text's.

# Faces of a tame polyfold

## The text, paraphrased

(Definition 17.3.7, p. 786) For a GCT `C` with a tame polyfold structure, a face of `C` is the
full subcategory `C_θ` associated to the closure `θ` in `|C|` of a connected component of
`{z ∈ |C| | d_{|C|}(z) = 1}`; `C` is face-structured if every `z ∈ |C|` lies in precisely
`d(z)` many `θ`.  For an sc-smooth model `X_Ψ` with `Γ_Ψ : X_Ψ → C`, `|Γ_Ψ| : |X_Ψ| → |C|` is a
homeomorphism preserving the degeneracy index, so the faces of `X_Ψ` (Definition 11.1.3) and of
`C` correspond, and the tame `C` is face-structured iff any of its models `X_Ψ` is.
(Proposition 17.3.8, p. 787) If the tame `C` is face-structured, every face is a subpolyfold.

## What is formalized (namespace `Polyfold.GCT.PolyfoldConstruction`)

* `degIndexVia c` (`d_{|C|}`, through the model `X_c` of a covering family `c`: the degeneracy
  index of `|X_c|` transported along `|Γ_c|`), `degIndexVia_eq` (**independent of `c`**),
  `degIndexVia_orbitMap` (`|Γ_c|` preserves it), `degIndexVia_π_obj` (`d_{|C|}(|Ψ(q)|) =
  d_O(q)` for every uniformizer `Ψ` of the family; `degIndexVia_π_obj_of_unif` for every
  uniformizer of `F`, through the family `c ⊕ {Ψ}`), `degIndexVia_π` (`d_{|C|}(|α|) = d(α)`,
  the degeneracy functor `degIndex` of Definition 17.1.30).
* **Definition 17.3.7**: `IsFaceVia c θ`, `faceSub θ` (the full subcategory `C_θ`),
  `IsFaceStructuredVia c`; `isFaceVia_congr`, `isFaceStructuredVia_congr` (independent of `c`).
* The correspondence after Definition 17.3.7: `isFaceVia_iff_isOrbitFace` (`θ` is a face of `C`
  iff `|Γ_{c'}|⁻¹(θ)` is a face of `X_{c'}`, for any two families), and
  `isFaceStructuredVia_iff` (for tame `C`: face-structured iff `X_{c'}` is face structured).
* **Proposition 17.3.8**: `proposition_17_3_8` (`C_θ` is a subpolyfold, Definitions 17.3.1 and
  17.3.2).
* Witness: `quadrantConstruction` (the trivial group on `[0,∞)² ⊕ W`) is tame and
  face-structured; the corner has `d = 2` and lies in a face, which is a subpolyfold
  (`quadrant_proposition_17_3_8`).

## Readings

* `d_{|C|}` is read as the degeneracy index of the model `|X_c|` along `|Γ_c|` for a covering
  family `c` (the text's "induced degeneracy index"); `degIndexVia_π` shows that it is
  the degeneracy functor `d` of Definition 17.1.30 on isomorphism classes.  The definitions take
  the family `c` as a parameter; every notion is independent of it (`degIndexVia_eq`), and a
  covering family exists exactly when the footprints cover `|C|`.
* "Tame polyfold structure" is `S.IsTame` (all `Ψ ∈ F` tame), included in
  `IsFaceStructuredVia`.  The models are tame then (`isTame_modelEpGroupoid`); the converse needs
  every `Ψ ∈ F` in a covering family, so the correspondence of face structures is stated for tame
  `C`, as in the text.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

universe u

namespace Polyfold

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} (S : C.PolyfoldConstruction)

/-! ### The degeneracy index of `|C|` -/

/-- **The degeneracy index `d_{|C|}`** (p. 786), through the sc-smooth model `X_c` of the covering
family `c`: `d_{|C|}(z) = d_{|X_c|}(|Γ_c|⁻¹(z))` (independent of `c`: `degIndexVia_eq`). -/
def degIndexVia (c : S.CoveringFamily) (z : C.toGroupoidStr.OrbitSpace) : ℕ :=
  (S.modelEP c.Ψ).X.degIndexOrbit ((S.modelOrbitHomeomorph c).symm z)

/-- `|Γ_c|` preserves the degeneracy index. -/
theorem degIndexVia_orbitMap (c : S.CoveringFamily) (w : (S.modelEP c.Ψ).X.OrbitSpace) :
    S.degIndexVia c ((S.modelFunctor c.Ψ).orbitMap w) = (S.modelEP c.Ψ).X.degIndexOrbit w := by
  rw [degIndexVia, ← S.modelOrbitHomeomorph_apply, Homeomorph.symm_apply_apply]

/-- **`d_{|C|}` does not depend on the covering family**: `|Γ_{c'}| ∘ |c → c'| = |Γ_c|` and the
comparison `X_c → X_{c'}` is a generalized isomorphism, which preserves `d` (Ch. 11). -/
theorem degIndexVia_eq (c c' : S.CoveringFamily) : S.degIndexVia c = S.degIndexVia c' := by
  funext z
  obtain ⟨w, rfl⟩ := (S.modelOrbitHomeomorph c).surjective z
  rw [S.modelOrbitHomeomorph_apply]
  calc S.degIndexVia c ((S.modelFunctor c.Ψ).orbitMap w)
      = (S.modelEP c.Ψ).X.degIndexOrbit w := S.degIndexVia_orbitMap c w
    _ = (S.modelEP c'.Ψ).X.degIndexOrbit (EPLocalization.EPLoc.orbitMap (S.comparison c c') w) :=
      (EPLocalization.EPLoc.degIndexOrbit_orbitMap (S.isGeneralizedIso_comparison c c') w).symm
    _ = S.degIndexVia c' ((S.modelFunctor c'.Ψ).orbitMap
          (EPLocalization.EPLoc.orbitMap (S.comparison c c') w)) :=
      (S.degIndexVia_orbitMap c' _).symm
    _ = S.degIndexVia c' ((S.modelFunctor c.Ψ).orbitMap w) :=
      congrArg (S.degIndexVia c') (congrFun (S.orbitMap_comparison c c') w)

/-- `d_{|C|}(|Ψ_i(q)|) = d_{O_i}(q)` for the uniformizers `Ψ_i` of the family. -/
theorem degIndexVia_π_obj (c : S.CoveringFamily) (i : c.ι) (q : (c.Ψ i).1.O) :
    S.degIndexVia c (C.toGroupoidStr.π ((c.Ψ i).1.obj q)) = (c.Ψ i).1.P.degIndex q := by
  have h := S.degIndexVia_orbitMap c ((S.modelEP c.Ψ).X.π ⟨i, q⟩)
  rw [S.modelOrbitMap_π] at h
  rw [h]
  exact MPolyfold.degIndex_sigma (fun j => (c.Ψ j).1.P) q

/-- The covering family `c ⊕ {Ψ}`. -/
def CoveringFamily.extend {S : C.PolyfoldConstruction} (c : S.CoveringFamily) (Ψ : S.Unif) :
    S.CoveringFamily where
  ι := c.ι ⊕ PUnit.{u + 1}
  Ψ := Sum.elim c.Ψ fun _ => Ψ
  cover := by
    refine eq_univ_of_forall fun z => ?_
    obtain ⟨_, ⟨i, rfl⟩, hz⟩ := (c.cover ▸ mem_univ z : z ∈ ⋃ i, (c.Ψ i).1.footprint)
    exact mem_iUnion.2 ⟨Sum.inl i, hz⟩

/-- **`d_{|C|}` is the degeneracy index of Definition 17.1.30**: `d_{|C|}(|Ψ(q)|) = d_O(q)` for
every uniformizer `Ψ` of `F`. -/
theorem degIndexVia_π_obj_of_unif (c : S.CoveringFamily) (Ψ : S.Unif) (q : Ψ.1.O) :
    S.degIndexVia c (C.toGroupoidStr.π (Ψ.1.obj q)) = Ψ.1.P.degIndex q := by
  rw [S.degIndexVia_eq c (c.extend Ψ)]
  exact S.degIndexVia_π_obj (c.extend Ψ) (Sum.inr PUnit.unit) q

/-- **`d_{|C|}` is the degeneracy functor of Definition 17.1.30 on orbits**:
`d_{|C|}(|α|) = d(α)` for every object `α`. -/
theorem degIndexVia_π (c : S.CoveringFamily) (α : C.Obj) :
    S.degIndexVia c (C.toGroupoidStr.π α) = S.degIndex α := by
  obtain ⟨_, ⟨i, rfl⟩, hz⟩ :=
    (c.cover ▸ mem_univ _ : C.toGroupoidStr.π α ∈ ⋃ i, (c.Ψ i).1.footprint)
  obtain ⟨q, hq⟩ := (c.Ψ i).1.mem_footprint_iff.1 hz
  rw [← hq, S.degIndexVia_π_obj c i q]
  exact (S.degIndex_eq (c.Ψ i) ((C.toGroupoidStr.π_eq_π_iff).1 hq)).symm

/-! ### Definition 17.3.7 -/

/-- **Definition 17.3.7** (p. 786): `θ ⊆ |C|` is (the orbit set of) a face of `C`: the closure of
a connected component of `{z | d_{|C|}(z) = 1}`. -/
def IsFaceVia (c : S.CoveringFamily) (θ : Set C.toGroupoidStr.OrbitSpace) : Prop :=
  ∃ z, S.degIndexVia c z = 1 ∧
    θ = closure (connectedComponentIn {w | S.degIndexVia c w = 1} z)

/-- **Definition 17.3.7**: the face `C_θ`, the full subcategory on `{α | |α| ∈ θ}`. -/
abbrev faceSub (θ : Set C.toGroupoidStr.OrbitSpace) :
    GroupoidStr (C.toGroupoidStr.π ⁻¹' θ) (C.toGroupoidStr.morOn (C.toGroupoidStr.π ⁻¹' θ)) :=
  C.toGroupoidStr.fullSub _

/-- **Definition 17.3.7**: `C` (with a tame polyfold structure) is **face-structured**: every
`z ∈ |C|` lies in precisely `d_{|C|}(z)` faces. -/
def IsFaceStructuredVia (c : S.CoveringFamily) : Prop :=
  S.IsTame ∧ ∀ z, {θ | S.IsFaceVia c θ ∧ z ∈ θ}.encard = S.degIndexVia c z

theorem isFaceVia_congr (c c' : S.CoveringFamily) (θ : Set C.toGroupoidStr.OrbitSpace) :
    S.IsFaceVia c θ ↔ S.IsFaceVia c' θ := by
  rw [IsFaceVia, IsFaceVia, S.degIndexVia_eq c c']

theorem isFaceStructuredVia_congr (c c' : S.CoveringFamily) :
    S.IsFaceStructuredVia c ↔ S.IsFaceStructuredVia c' := by
  simp only [IsFaceStructuredVia, S.isFaceVia_congr c c', S.degIndexVia_eq c c']

theorem isFaceVia_iff_isFaceIn (c : S.CoveringFamily) (θ : Set C.toGroupoidStr.OrbitSpace) :
    S.IsFaceVia c θ ↔ TameBoundary.IsFaceIn (S.degIndexVia c) univ θ := by
  simp only [TameBoundary.IsFaceIn, TameBoundary.faceAt, IsFaceVia, univ_inter, mem_univ,
    true_and]

theorem isFaceStructuredVia_iff_isFaceStructuredOpen (c : S.CoveringFamily) :
    S.IsFaceStructuredVia c ↔
      S.IsTame ∧ TameBoundary.IsFaceStructuredOpen (S.degIndexVia c) univ := by
  simp only [IsFaceStructuredVia, TameBoundary.IsFaceStructuredOpen, TameBoundary.facesThrough,
    isFaceVia_iff_isFaceIn, isOpen_univ, mem_univ, true_and, forall_const]

/-! ### The correspondence with the faces of the models -/

/-- **The faces of `C` and of `X_{c'}` correspond** (p. 786): `θ` is a face of `C` iff
`|Γ_{c'}|⁻¹(θ)` is a face of the ep-groupoid `X_{c'}` (Definition 11.1.3). -/
theorem isFaceVia_iff_isOrbitFace (c c' : S.CoveringFamily) (θ : Set C.toGroupoidStr.OrbitSpace) :
    S.IsFaceVia c θ ↔ (S.modelEP c'.Ψ).X.IsOrbitFace ((S.modelFunctor c'.Ψ).orbitMap ⁻¹' θ) := by
  have he : IsHomeomorph (S.modelFunctor c'.Ψ).orbitMap := (S.modelOrbitHomeomorph c').isHomeomorph
  have hd := S.degIndexVia_orbitMap c'
  rw [S.isFaceVia_congr c c', isFaceVia_iff_isFaceIn, EpGroupoid.isOrbitFace_iff_isFaceIn]
  constructor
  · exact TameBoundary.exists_isFaceIn_univ_preimage he hd
  · intro h
    have h' := TameBoundary.isFaceIn_univ_image he hd h
    rwa [image_preimage_eq _ he.surjective] at h'

/-- **The tame `C` is face-structured iff any of its models `X_{c'}` is** (p. 787, "this follows
from the discussion after Definition 11.1.3"). -/
theorem isFaceStructuredVia_iff (hT : S.IsTame) (c c' : S.CoveringFamily) :
    S.IsFaceStructuredVia c ↔ (S.modelEP c'.Ψ).X.IsEpFaceStructured := by
  rw [S.isFaceStructuredVia_congr c c', isFaceStructuredVia_iff_isFaceStructuredOpen,
    EpGroupoid.isEpFaceStructured_iff,
    TameBoundary.isFaceStructuredOpen_univ_iff (S.modelOrbitHomeomorph c').isHomeomorph
      (S.degIndexVia_orbitMap c')]
  exact ⟨fun h => ⟨S.isTame_modelEpGroupoid c'.Ψ hT, h.2⟩, fun h => ⟨hT, h.2⟩⟩

/-! ### Proposition 17.3.8 -/

/-- `π⁻¹(θ)` is saturated. -/
theorem isSaturated_π_preimage (θ : Set C.toGroupoidStr.OrbitSpace) :
    C.toGroupoidStr.IsSaturated (C.toGroupoidStr.π ⁻¹' θ) :=
  C.toGroupoidStr.isSaturated_iff.2 fun φ hφ => by
    change C.toGroupoidStr.π (C.toGroupoidStr.tgt φ) ∈ θ
    rw [← C.toGroupoidStr.π_src_eq_π_tgt φ]
    exact hφ

/-- **Proposition 17.3.8** (p. 787): if the tame `C` is face-structured, every face `C_θ` is a
subpolyfold, in the sense of Definition 17.3.2 (in every model `X_{c'}` the preimage is the face
`X_θ` of Definition 11.1.3, an ep-subgroupoid by Ch. 11) and of Definition 17.3.1. -/
theorem proposition_17_3_8 (c : S.CoveringFamily) (hF : S.IsFaceStructuredVia c)
    {θ : Set C.toGroupoidStr.OrbitSpace} (hθ : S.IsFaceVia c θ) :
    S.IsSubpolyfoldModel (C.toGroupoidStr.π ⁻¹' θ) ∧ S.IsSubpolyfold (C.toGroupoidStr.π ⁻¹' θ) := by
  have hX := (S.isFaceStructuredVia_iff hF.1 c c).1 hF
  have hθ' := (S.isFaceVia_iff_isOrbitFace c c θ).1 hθ
  have hm : S.IsSubpolyfoldModel (C.toGroupoidStr.π ⁻¹' θ) :=
    ⟨isSaturated_π_preimage θ, c, EpGroupoid.isEpSubgroupoid_faceObj hX hθ'⟩
  exact ⟨hm, S.isSubpolyfold_of_isSubpolyfoldModel hm⟩

/-! ### Witness: the quadrant `[0,∞)² ⊕ W` -/

section QuadrantWitness

open MPolyfold TameBoundaryExample

variable (W : ScBanach)

/-- The trivial action of the trivial group on `[0,∞)² ⊕ W`. -/
@[reducible]
def quadrantTrivialAction : MulAction Unit (quadrant 2 W 0) where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

attribute [local instance] quadrantTrivialAction

theorem quadrant_isScSmoothMap_smul (k : Unit) :
    (quadrantPolyfold 2 W).IsScSmoothMap (quadrantPolyfold 2 W) fun y => k • y :=
  isScSmoothMap_id

/-- **The quadrant polyfold**: the translation GCT of the trivial group on `[0,∞)² ⊕ W`, with
`F(x) = {Ψ₀}` (Definition 17.1.8). -/
abbrev quadrantConstruction :
    (GCT.translation Unit (quadrant 2 W 0) (quadrant_isScSmoothMap_smul W)).PolyfoldConstruction :=
  twistConstruction (quadrant_isScSmoothMap_smul W) (TranslationTwist.refl Unit _)

/-- The corner `0` of the quadrant. -/
abbrev quadrantCorner : quadrant 2 W 0 := ⟨0, zero_mem_quadrant 2 W⟩

/-- The tautological uniformizer of the quadrant polyfold. -/
abbrev quadrantUnif : (quadrantConstruction W).Unif := tautUnif _ _ (quadrantCorner W)

theorem quadrantUnif_footprint : (quadrantUnif W).1.footprint = univ := by
  refine eq_univ_of_forall fun z => ?_
  induction z using Quotient.inductionOn with
  | h x => exact (quadrantUnif W).1.mem_footprint_iff.2 ⟨x, rfl⟩

/-- The tautological uniformizer, a covering family. -/
def quadrantFamily : (quadrantConstruction W).CoveringFamily where
  ι := Unit
  Ψ := fun _ => quadrantUnif W
  cover := eq_univ_of_forall fun z => mem_iUnion.2 ⟨(), by
    rw [quadrantUnif_footprint]
    exact mem_univ z⟩

/-- `π : [0,∞)² ⊕ W → |C|` is a homeomorphism (the group is trivial). -/
theorem quadrant_isHomeomorph_π :
    IsHomeomorph (GroupoidStr.translation Unit (quadrant 2 W 0)).π := by
  refine ⟨continuous_quot_mk, GroupoidStr.isOpenMap_π_translation fun _ => continuous_id,
    fun x y h => ?_, GroupoidStr.surjective_π _⟩
  obtain ⟨φ, hs, ht⟩ := ((GroupoidStr.translation Unit (quadrant 2 W 0)).π_eq_π_iff).1 h
  change φ.2 = x at hs
  change φ.2 = y at ht
  rw [← hs, ht]

theorem quadrant_degIndexVia (q : quadrant 2 W 0) :
    (quadrantConstruction W).degIndexVia (quadrantFamily W)
      ((GroupoidStr.translation Unit (quadrant 2 W 0)).π q) = dq 2 W q :=
  (quadrantConstruction W).degIndexVia_π_obj_of_unif (quadrantFamily W) (quadrantUnif W) q

/-- **The non-degenerate witness of Definition 17.3.7 and Proposition 17.3.8**: the quadrant
polyfold is tame and face-structured; its corner has `d_{|C|} = 2` and lies in exactly two faces;
a face through the corner is a subpolyfold (Definitions 17.3.1 and 17.3.2). -/
theorem quadrant_proposition_17_3_8 :
    (quadrantConstruction W).IsTame ∧
      (quadrantConstruction W).IsFaceStructuredVia (quadrantFamily W) ∧
      (quadrantConstruction W).degIndexVia (quadrantFamily W)
        ((GroupoidStr.translation Unit (quadrant 2 W 0)).π (quadrantCorner W)) = 2 ∧
      {θ | (quadrantConstruction W).IsFaceVia (quadrantFamily W) θ ∧
        (GroupoidStr.translation Unit (quadrant 2 W 0)).π (quadrantCorner W) ∈ θ}.encard = 2 ∧
      ∃ θ, (quadrantConstruction W).IsFaceVia (quadrantFamily W) θ ∧
        (GroupoidStr.translation Unit (quadrant 2 W 0)).π (quadrantCorner W) ∈ θ ∧
        (quadrantConstruction W).IsSubpolyfoldModel
          ((GroupoidStr.translation Unit (quadrant 2 W 0)).π ⁻¹' θ) ∧
        (quadrantConstruction W).IsSubpolyfold
          ((GroupoidStr.translation Unit (quadrant 2 W 0)).π ⁻¹' θ) := by
  have hT : (quadrantConstruction W).IsTame :=
    twistConstruction_isTame _ _ (quadrantPolyfold_isTame 2 W)
  have hF : (quadrantConstruction W).IsFaceStructuredVia (quadrantFamily W) :=
    ((quadrantConstruction W).isFaceStructuredVia_iff_isFaceStructuredOpen _).2
      ⟨hT, (TameBoundary.isFaceStructuredOpen_univ_iff (quadrant_isHomeomorph_π W)
        (quadrant_degIndexVia W)).1 (isFaceStructuredOpen_quadrant isOpen_univ)⟩
  have h2 : (quadrantConstruction W).degIndexVia (quadrantFamily W)
      ((GroupoidStr.translation Unit (quadrant 2 W 0)).π (quadrantCorner W)) = 2 :=
    (quadrant_degIndexVia W _).trans (quadrantPolyfold_degIndex_zero 2 W)
  have hc := hF.2 ((GroupoidStr.translation Unit (quadrant 2 W 0)).π (quadrantCorner W))
  rw [h2] at hc
  obtain ⟨θ, hθ, hz⟩ := nonempty_of_encard_ne_zero (s := {θ | (quadrantConstruction W).IsFaceVia
    (quadrantFamily W) θ ∧
      (GroupoidStr.translation Unit (quadrant 2 W 0)).π (quadrantCorner W) ∈ θ})
    (by rw [hc]; exact two_ne_zero)
  exact ⟨hT, hF, h2, hc, θ, hθ, hz, (quadrantConstruction W).proposition_17_3_8 _ hF hθ⟩

end QuadrantWitness

end GCT.PolyfoldConstruction

end Polyfold
