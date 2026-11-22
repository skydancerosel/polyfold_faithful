import Polyfold.Chapter17.BranchedSubcategory
import Polyfold.Chapter16.SuppNaturality
import Polyfold.Chapter17.PolyfoldConstructionExamples

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.5, **Proposition 17.5.5** (p. 814) with (17.85).  Numbers and pages are the 2021 text's.

# The manifold and orbifold structure on `|supp(Θ)|`

## The text, paraphrased

(Proposition 17.5.5) For a branched ep⁺-subcategory `Θ` of `C`: (1) if `Θ` is of manifold-type,
`S = |supp(Θ)|` has a natural structure of a smooth finite-dimensional manifold (the
M⁺-polyfold version); (2) if `Θ` is of orbifold-type, `S` has a natural smooth orbifold structure.
*Proof* (text): `Θ ∘ Γ` is of manifold- or orbifold-type iff `Θ` is; for a second covering family,
the canonical generalized isomorphism `f : X → X'` has `|Γ| = |Γ'| ∘ |f|` (17.85) and
`Θ ∘ Γ' = f_*(Θ ∘ Γ)`; for manifold-type `|f|` induces a diffeomorphism
`|supp(Θ ∘ Γ)| → |supp(Θ ∘ Γ')|`, and there is a unique manifold structure on `|supp(Θ)|` for which
`|Γ| : |supp(Θ ∘ Γ)| → |supp(Θ)|` is a diffeomorphism, independent of the family.  For orbifold
type "the argument is similar and `|f|` is a smooth orbifold map.  Details are left to the reader."

## What is formalized

* `EpGroupoid.IsSuppStructure X Θ PZ`: `PZ` is a structure of Proposition 9.1.9 (1) on
  `|supp(Θ)|` (`supp(Θ)` an ep-subgroupoid and a smooth submanifold, and `a ↦ |a|` a local
  sc-diffeomorphism `supp(Θ) → |supp(Θ)|`).
* For a generalized isomorphism `f : X → Y` and a branched `Θ'` of orbifold-type on `Y`:
  `EPLoc.orbitSuppMap` (the restriction `|supp(f^*Θ')| → |supp(Θ')|` of `|f|`),
  `EPLoc.isScSmoothOn_orbitSuppMap` (it is sc-smooth for any structures of Proposition 9.1.9 (1);
  the argument of Proposition 16.4.3, Chapter 16, through the restrictions of the equivalences of
  a representative to the supports), and `EPLoc.restrictSupp_orbifold` (the restrictions of the
  representative to the sub-ep-groupoids on the supports are equivalences, compatible with `|f|`:
  "`|f|` is a smooth orbifold map").
* `suppHomeomorph c` (`|supp(Γ^*Θ)| ≃ₜ |supp(Θ)|`, the restriction of `|Γ|`),
  `suppHomeomorph_orbitSuppMap` (`|Γ'| ∘ |f| = |Γ|` on the supports, (17.85)).
* **`proposition_17_5_5_one`**: for `Θ` of manifold-type, every covering family induces a
  structure on `|supp(Θ)|` (Proposition 9.1.9 (1) through `|Γ|`), and the structures induced by
  any two covering families (and any choices) agree: the identity is an sc-diffeomorphism.
* **`proposition_17_5_5_two`**: for `Θ` of orbifold-type, `supp(Γ^*Θ)` is an ep-subgroupoid of
  `X_Ψ` whose orbit space is homeomorphic to `|supp(Θ)|` (through `|Γ|`), and for two covering
  families the two ep-groupoids are related by a pair of equivalences from a third one, compatible
  with the homeomorphisms (a generalized isomorphism inducing the identity of `|supp(Θ)|`).

## Readings

* "Smooth manifold" is read, as in Proposition 9.1.9 (1) and Remark 9.1.10, as an M-polyfold
  structure locally sc-diffeomorphic to the smooth finite-dimensional submanifold `supp(Θ ∘ Γ)`;
  "natural" as: induced through `|Γ|` from Proposition 9.1.9 (1), for some covering family; the
  uniqueness claim as the statement that all such structures agree.
* The orbifold structure "up to equivalence" is the sub-ep-groupoid on the support together with
  the homeomorphism of its orbit space onto `|supp(Θ)|` (Proposition 9.1.9 (2)); its independence
  is the existence of the equivalences above.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology CategoryTheory

noncomputable section

namespace Polyfold

universe u

open EpGroupoid MPolyfold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- **The structure of Proposition 9.1.9 (1) on `|supp(Θ)|`**: `supp(Θ)` is an ep-subgroupoid and
a smooth submanifold of `X`, and `PZ` makes `p : supp(Θ) → |supp(Θ)|`, `a ↦ |a|`, a local
sc-diffeomorphism. -/
def IsSuppStructure (Θ : Obj → ℚ) [ParacompactSpace (X.orbitSupp Θ)]
    (PZ : MPolyfold (X.orbitSupp Θ)) : Prop :=
  ∃ hA : X.IsEpSubgroupoid (supp Θ), X.PObj.IsSmoothSubmanifold (supp Θ) ∧
    haveI := X.PObj.paracompactSpace_subtype (supp Θ)
    (subEpGroupoid hA).PObj.IsLocalScDiffeo PZ (X.orbitSuppProj Θ)

variable {X}

/-- **Proposition 9.1.9 (1)** in the form of `IsSuppStructure`. -/
theorem exists_isSuppStructure {Θ : Obj → ℚ} (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hm : X.IsManifoldType Θ) :
    haveI := hΘ.paracompactSpace_orbitSupp
    ∃ PZ : MPolyfold (X.orbitSupp Θ), X.IsSuppStructure Θ PZ := by
  have := hΘ.paracompactSpace_orbitSupp
  obtain ⟨hA, hsub, PZ, hPZ⟩ := X.proposition_9_1_9_one hΘ hm
  exact ⟨PZ, hA, hsub, hPZ⟩

end EpGroupoid

namespace EPLocalization.EPLoc

variable {X Y : EP.{u}}

/-- `|f|` maps `|supp(Θ)|` into `|supp(Θ')|` for `Θ = f^*Θ'`. -/
theorem mapsTo_orbitMap_orbitSupp {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) {Θ' : Y.Obj → ℚ}
    (hΘ' : Y.X.IsFunctorial Θ') {Θ : X.Obj → ℚ} (hpull : pullTheta f Θ' = Θ) :
    MapsTo (orbitMap f) (X.X.orbitSupp Θ) (Y.X.orbitSupp Θ') := by
  subst hpull
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy⟩ := Y.X.surjective_π (orbitMap f (X.X.π x))
  refine ⟨y, ?_, hy⟩
  change 0 < Θ' y
  rw [← pullTheta_eq_of_orbitMap hf hΘ' hy.symm]
  exact hx

/-- **The restriction `|supp(Θ)| → |supp(Θ')|` of `|f|`** for `Θ = f^*Θ'`. -/
def orbitSuppMap {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) {Θ' : Y.Obj → ℚ}
    (hΘ' : Y.X.IsFunctorial Θ') {Θ : X.Obj → ℚ} (hpull : pullTheta f Θ' = Θ) :
    X.X.orbitSupp Θ → Y.X.orbitSupp Θ' :=
  (mapsTo_orbitMap_orbitSupp hf hΘ' hpull).restrict _ _ _

@[simp] theorem orbitSuppMap_val {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) {Θ' : Y.Obj → ℚ}
    (hΘ' : Y.X.IsFunctorial Θ') {Θ : X.Obj → ℚ} (hpull : pullTheta f Θ' = Θ)
    (q : X.X.orbitSupp Θ) : (orbitSuppMap hf hΘ' hpull q : Y.X.OrbitSpace) = orbitMap f q := rfl

/-- **The restrictions of a representative to the supports** (2021 p. 814, "`|f|` is a smooth
orbifold map"): for a generalized isomorphism `f = [X ←F A →Φ Y]`, a branched `Θ'` of
orbifold-type and `Θ = f^*Θ'`, the functors `F`, `Φ` are equivalences, `supp(Φ^*Θ')` is
`F⁻¹(supp(Θ))` and `Φ⁻¹(supp(Θ'))`, and `|f| ∘ |F| = |Φ|`; so `F`, `Φ` restrict to equivalences of
the ep-subgroupoids on the supports (`EpFunctor.IsEquivalence.restrictSub`). -/
theorem restrictSupp_orbifold {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) {Θ' : Y.Obj → ℚ}
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (ho' : IsOrbifoldType Θ') {Θ : X.Obj → ℚ}
    (hpull : pullTheta f Θ' = Θ) :
    ∃ (A : EP.{u}) (F : EpFunctor A.X X.X) (Φ : EpFunctor A.X Y.X) (ΘA : A.Obj → ℚ),
      F.IsEquivalence ∧ Φ.IsEquivalence ∧ A.X.IsBranchedEpSubgroupoid ΘA ∧ IsOrbifoldType ΘA ∧
      (∀ b, b ∈ supp ΘA ↔ F.obj b ∈ supp Θ) ∧
      (∀ b, b ∈ supp ΘA ↔ Φ.obj b ∈ supp Θ') ∧
      ∀ b, orbitMap f (X.X.π (F.obj b)) = Y.X.π (Φ.obj b) := by
  subst hpull
  set d := rep f
  have hF := d.isEquivalence_F
  have hΦ := isEquivalence_rep_Φ hf
  set ΘA := d.Φ.pullbackTheta Θ'
  have hΘA := EpFunctor.isBranchedEpSubgroupoid_pullbackTheta hΦ hΘ'
  refine ⟨d.A, d.F, d.Φ, ΘA, hF, hΦ, hΘA, fun x => ho' (d.Φ.obj x), fun b => ?_,
    fun _ => Iff.rfl, fun b => ?_⟩
  · change 0 < ΘA b ↔ 0 < d.F.pushforwardTheta ΘA (d.F.obj b)
    rw [EpFunctor.pushforwardTheta_obj hF.full hΘA.isFunctorial]
  · rw [orbitMap_eq_rep]
    exact ((rep f).orbitMap_orbitMap_F (d.A.X.π b))

/-- **`|f| : |supp(Θ)| → |supp(Θ')|` is sc-smooth** (`Θ = f^*Θ'`) for any structures of
Proposition 9.1.9 (1) (2021 p. 814; the argument of Proposition 16.4.3), when `Θ'` is of
orbifold-type.  Near `|F(b)|` it is `p' ∘ Φ|supp ∘ (F|supp)⁻¹ ∘ p⁻¹`. -/
theorem isScSmoothOn_orbitSuppMap {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) {Θ' : Y.Obj → ℚ}
    (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') (ho' : IsOrbifoldType Θ') {Θ : X.Obj → ℚ}
    (hpull : pullTheta f Θ' = Θ)
    [ParacompactSpace (X.X.orbitSupp Θ)] [ParacompactSpace (Y.X.orbitSupp Θ')]
    {PZ : MPolyfold (X.X.orbitSupp Θ)} {PZ' : MPolyfold (Y.X.orbitSupp Θ')}
    (hPZ : X.X.IsSuppStructure Θ PZ) (hPZ' : Y.X.IsSuppStructure Θ' PZ') :
    PZ.IsScSmoothOn PZ' (orbitSuppMap hf hΘ'.isFunctorial hpull) univ := by
  classical
  obtain ⟨hA, -, hloc⟩ := hPZ
  obtain ⟨hA', -, hloc'⟩ := hPZ'
  have := X.X.PObj.paracompactSpace_subtype (EpGroupoid.supp Θ)
  have := Y.X.PObj.paracompactSpace_subtype (EpGroupoid.supp Θ')
  obtain ⟨A, F, Φ, ΘA, hF, hΦ, hΘA, hoA, hmemF, hmemΦ, horb⟩ :=
    restrictSupp_orbifold hf hΘ' ho' hpull
  have hSA := isEpSubgroupoid_supp_of_isOrbifoldType hΘA hoA
  have := A.X.PObj.paracompactSpace_subtype (EpGroupoid.supp ΘA)
  set Fs := F.restrictSub hSA hA hmemF
  set Φs := Φ.restrictSub hSA hA' hmemΦ
  have hFs := (hF.restrictSub hSA hA hmemF).isLocalScDiffeo_obj
  have hΦs := Φs.isScSmoothMap_obj
  have key : ∀ b : EpGroupoid.supp ΘA,
      orbitSuppMap hf hΘ'.isFunctorial hpull (X.X.orbitSuppProj Θ (Fs.obj b)) =
      Y.X.orbitSuppProj Θ' (Φs.obj b) := fun b => Subtype.ext (horb b.1)
  refine IsScSmoothOn.of_locally isOpen_univ fun q _ => ?_
  obtain ⟨b, rfl⟩ : ∃ b : EpGroupoid.supp ΘA, X.X.orbitSuppProj Θ (Fs.obj b) = q := by
    obtain ⟨_, x, hx, rfl⟩ := q
    obtain ⟨y, ψ, hs, ht⟩ := hF.exists_iso x
    have hψs : X.X.src ψ ∈ EpGroupoid.supp Θ :=
      src_mem_of_tgt_mem_of_isSaturated hA.isSaturated (by rw [ht]; exact hx)
    have hy : y ∈ EpGroupoid.supp ΘA := (hmemF y).2 (hs ▸ hψs)
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    change X.X.π (F.obj y) = X.X.π x
    exact (GroupoidStr.π_eq_π_iff _).2 ⟨ψ, hs, ht⟩
  obtain ⟨U₁, V₁, g₁, hU₁, hd₁⟩ := hloc (Fs.obj b)
  obtain ⟨U₂, V₂, g₂, hU₂, hd₂⟩ := hFs b
  set V := V₁ ∩ g₁ ⁻¹' V₂
  have hV : IsOpen V := hd₁.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage
    hd₁.isScSmoothOn_inv.isOpen hd₂.isScSmoothOn_inv.isOpen
  have hqV : X.X.orbitSuppProj Θ (Fs.obj b) ∈ V := by
    refine ⟨hd₁.mapsTo hU₁, ?_⟩
    change g₁ _ ∈ V₂
    rw [hd₁.left_inv _ hU₁]
    exact hd₂.mapsTo hU₂
  refine ⟨V, hV, hqV, subset_univ _, ?_⟩
  have hg₁ : PZ.IsScSmoothOn (subEpGroupoid hA).PObj g₁ V :=
    hd₁.isScSmoothOn_inv.mono hV inter_subset_left
  have hg₂ := IsScSmoothOn.comp hd₂.isScSmoothOn_inv hg₁ fun z hz => hz.2
  have hΦg := IsScSmoothOn.comp hΦs hg₂ (mapsTo_univ _ _)
  have hG := IsScSmoothOn.comp (hloc'.isScSmoothMap) hΦg (mapsTo_univ _ _)
  refine hG.congr fun z hz => ?_
  have h2 : X.X.orbitSuppProj Θ (g₁ z) = z := hd₁.right_inv z hz.1
  have h3 : Fs.obj (g₂ (g₁ z)) = g₁ z := hd₂.right_inv _ hz.2
  change Y.X.orbitSuppProj Θ' (Φs.obj (g₂ (g₁ z))) = orbitSuppMap hf hΘ'.isFunctorial hpull z
  rw [← key, h3, h2]

end EPLocalization.EPLoc

namespace GCT.PolyfoldConstruction

open EPLocalization EPLocalization.EPLoc

variable {C : GCT.{u}} {S : C.PolyfoldConstruction} {Θ : C.Obj → ℚ}

instance paracompactSpace_orbitSuppC (Θ : C.Obj → ℚ) :
    ParacompactSpace (C.toGroupoidStr.orbitSupp Θ) :=
  paracompactSpace_of_metrizableSpace _

instance paracompactSpace_modelOrbitSubset {ι : Type u} (Ψ : ι → S.Unif)
    (A : Set (S.modelEP Ψ).X.OrbitSpace) : ParacompactSpace A :=
  paracompactSpace_model_subset A

variable (S) in
/-- **`|Γ| : |supp(Γ^*Θ)| ≃ₜ |supp(Θ)|`**, the restriction of the homeomorphism `|Γ_Ψ|` of Lemma
17.1.15 (2021 p. 814). -/
def suppHomeomorph (c : S.CoveringFamily) (hΘ : C.toGroupoidStr.IsFunctorial Θ) :
    (S.modelEP c.Ψ).X.orbitSupp (S.modelPull c.Ψ Θ) ≃ₜ C.toGroupoidStr.orbitSupp Θ :=
  ((S.modelOrbitHomeomorph c).image _).trans
    (Homeomorph.setCongr (image_modelOrbitMap_orbitSupp c.cover hΘ))

@[simp] theorem suppHomeomorph_val (c : S.CoveringFamily) (hΘ : C.toGroupoidStr.IsFunctorial Θ)
    (q : (S.modelEP c.Ψ).X.orbitSupp (S.modelPull c.Ψ Θ)) :
    (S.suppHomeomorph c hΘ q : C.toGroupoidStr.OrbitSpace) = (S.modelFunctor c.Ψ).orbitMap q :=
  rfl

/-- **(17.85) on the supports**: `|Γ'| ∘ |f| = |Γ|` on `|supp(Γ^*Θ)|`, `f = f_{Ψ,Ψ'}`. -/
theorem suppHomeomorph_orbitSuppMap (c c' : S.CoveringFamily)
    (hΘ : C.toGroupoidStr.IsFunctorial Θ)
    (q : (S.modelEP c.Ψ).X.orbitSupp (S.modelPull c.Ψ Θ)) :
    S.suppHomeomorph c' hΘ (orbitSuppMap (S.isGeneralizedIso_comparison c c')
      (isFunctorial_modelPull hΘ) (pullTheta_comparison_modelPull c c' hΘ) q) =
      S.suppHomeomorph c hΘ q :=
  Subtype.ext (congrFun (S.orbitMap_comparison c c') q.1)

/-- One direction of the independence in Proposition 17.5.5 (1). -/
theorem isScSmoothOn_id_transport (hΘ : S.IsBranchedSubcategory Θ) (ho : C.IsOrbifoldTypeBranched Θ)
    (c c' : S.CoveringFamily) {PZ : MPolyfold ((S.modelEP c.Ψ).X.orbitSupp (S.modelPull c.Ψ Θ))}
    {PZ' : MPolyfold ((S.modelEP c'.Ψ).X.orbitSupp (S.modelPull c'.Ψ Θ))}
    (hPZ : (S.modelEP c.Ψ).X.IsSuppStructure _ PZ)
    (hPZ' : (S.modelEP c'.Ψ).X.IsSuppStructure _ PZ') :
    (PZ.transport (S.suppHomeomorph c hΘ.isFunctorial)).IsScSmoothOn
      (PZ'.transport (S.suppHomeomorph c' hΘ.isFunctorial)) id univ := by
  have hf := S.isGeneralizedIso_comparison c c'
  have hpull := pullTheta_comparison_modelPull c c' hΘ.isFunctorial
  have ht := isScSmoothOn_orbitSuppMap hf (proposition_17_5_2_two (Ψ := c'.Ψ) hΘ)
    ((isOrbifoldType_modelPull_iff c' hΘ.isFunctorial).2 ho) hpull hPZ hPZ'
  have h1 := (PZ.isScDiffeoOn_transport (S.suppHomeomorph c hΘ.isFunctorial)).isScSmoothOn_inv
  have h2 := (PZ'.isScDiffeoOn_transport (S.suppHomeomorph c' hΘ.isFunctorial)).isScSmoothOn
  have hcomp := IsScSmoothOn.comp h2 (IsScSmoothOn.comp ht h1 (mapsTo_univ _ _))
    (mapsTo_univ _ _)
  refine hcomp.congr fun z _ => ?_
  change S.suppHomeomorph c' hΘ.isFunctorial (orbitSuppMap hf _ hpull
    ((S.suppHomeomorph c hΘ.isFunctorial).symm z)) = z
  rw [suppHomeomorph_orbitSuppMap, Homeomorph.apply_symm_apply]

/-- **Proposition 17.5.5 (1)** (2021 p. 814): for a branched ep⁺-subcategory `Θ` of
manifold-type, every covering family induces on `|supp(Θ)| ⊆ |C|` a structure of Proposition
9.1.9 (1) through `|Γ| : |supp(Γ^*Θ)| ≃ₜ |supp(Θ)|` (the smooth manifold structure, M⁺-polyfold
version), and the structures induced by any two covering families and any two such choices agree:
the identity of `|supp(Θ)|` is an sc-diffeomorphism between them. -/
theorem proposition_17_5_5_one (hΘ : S.IsBranchedSubcategory Θ)
    (hm : C.IsManifoldTypeBranched Θ) :
    (∀ c : S.CoveringFamily, ∃ PZ : MPolyfold ((S.modelEP c.Ψ).X.orbitSupp (S.modelPull c.Ψ Θ)),
      (S.modelEP c.Ψ).X.IsSuppStructure _ PZ) ∧
    ∀ (c c' : S.CoveringFamily)
      (PZ : MPolyfold ((S.modelEP c.Ψ).X.orbitSupp (S.modelPull c.Ψ Θ)))
      (PZ' : MPolyfold ((S.modelEP c'.Ψ).X.orbitSupp (S.modelPull c'.Ψ Θ))),
      (S.modelEP c.Ψ).X.IsSuppStructure _ PZ → (S.modelEP c'.Ψ).X.IsSuppStructure _ PZ' →
      (PZ.transport (S.suppHomeomorph c hΘ.isFunctorial)).IsScDiffeoOn
        (PZ'.transport (S.suppHomeomorph c' hΘ.isFunctorial)) id id univ univ := by
  refine ⟨fun c => ?_, fun c c' PZ PZ' hPZ hPZ' => ?_⟩
  · obtain ⟨hA, hsub, PZ, hPZ⟩ := (S.modelEP c.Ψ).X.proposition_9_1_9_one
      (proposition_17_5_2_two hΘ) ((isManifoldType_modelPull_iff c hΘ.isFunctorial).2 hm)
    exact ⟨PZ, hA, hsub, hPZ⟩
  · exact ⟨isScSmoothOn_id_transport hΘ hm.1 c c' hPZ hPZ',
      isScSmoothOn_id_transport hΘ hm.1 c' c hPZ' hPZ, mapsTo_univ _ _, mapsTo_univ _ _,
      fun _ _ => rfl, fun _ _ => rfl⟩

/-- **Proposition 17.5.5 (2)** (2021 p. 814; "details are left to the reader"): for a branched
ep⁺-subcategory `Θ` of orbifold-type and a covering family, `supp(Γ^*Θ)` is an ep-subgroupoid and
a smooth submanifold of `X_Ψ` whose orbit space is homeomorphic to `|supp(Θ)|` through `|Γ|`
(Proposition 9.1.9 (2)); and for two covering families there are an ep-groupoid `A`, equivalences
`F : A → X_Ψ`, `Φ : A → X_Ψ'` with `|Γ ∘ F| = |Γ' ∘ Φ|` and a branched `Θ_A` of orbifold-type with
`supp(Θ_A) = F⁻¹ supp(Γ^*Θ) = Φ⁻¹ supp(Γ'^*Θ)`, so that `F`, `Φ` restrict to equivalences of the
ep-subgroupoids on the supports: the two orbifold structures are equivalent, inducing the
identity of `|supp(Θ)|`. -/
theorem proposition_17_5_5_two (hΘ : S.IsBranchedSubcategory Θ)
    (ho : C.IsOrbifoldTypeBranched Θ) :
    (∀ c : S.CoveringFamily,
      ∃ hA : (S.modelEP c.Ψ).X.IsEpSubgroupoid (supp (S.modelPull c.Ψ Θ)),
        (S.modelEP c.Ψ).X.PObj.IsSmoothSubmanifold (supp (S.modelPull c.Ψ Θ)) ∧
        haveI := (S.modelEP c.Ψ).X.PObj.paracompactSpace_subtype (supp (S.modelPull c.Ψ Θ))
        ∃ e : (subEpGroupoid hA).OrbitSpace ≃ₜ C.toGroupoidStr.orbitSupp Θ,
          ∀ x : supp (S.modelPull c.Ψ Θ),
            (e ((subEpGroupoid hA).π x) : C.toGroupoidStr.OrbitSpace) =
              C.toGroupoidStr.π ((S.modelFunctor c.Ψ).obj x.1)) ∧
    ∀ c c' : S.CoveringFamily,
      ∃ (A : EP.{u}) (F : EpFunctor A.X (S.modelEP c.Ψ).X)
        (Φ : EpFunctor A.X (S.modelEP c'.Ψ).X) (ΘA : A.Obj → ℚ),
        F.IsEquivalence ∧ Φ.IsEquivalence ∧ A.X.IsBranchedEpSubgroupoid ΘA ∧
        IsOrbifoldType ΘA ∧ (∀ b, b ∈ supp ΘA ↔ F.obj b ∈ supp (S.modelPull c.Ψ Θ)) ∧
        (∀ b, b ∈ supp ΘA ↔ Φ.obj b ∈ supp (S.modelPull c'.Ψ Θ)) ∧
        ∀ b, C.toGroupoidStr.π ((S.modelFunctor c.Ψ).obj (F.obj b)) =
          C.toGroupoidStr.π ((S.modelFunctor c'.Ψ).obj (Φ.obj b)) := by
  refine ⟨fun c => ?_, fun c c' => ?_⟩
  · obtain ⟨hA, hsub, e, he⟩ := (S.modelEP c.Ψ).X.proposition_9_1_9_two
      (proposition_17_5_2_two hΘ) ((isOrbifoldType_modelPull_iff c hΘ.isFunctorial).2 ho)
    exact ⟨hA, hsub, e.trans (S.suppHomeomorph c hΘ.isFunctorial), fun x => by
      change (S.modelFunctor c.Ψ).orbitMap (e _ : (S.modelEP c.Ψ).X.OrbitSpace) = _
      exact congrArg (S.modelFunctor c.Ψ).orbitMap (he x)⟩
  · obtain ⟨A, F, Φ, ΘA, hF, hΦ, hΘA, hoA, hmF, hmΦ, horb⟩ :=
      restrictSupp_orbifold (S.isGeneralizedIso_comparison c c')
        (proposition_17_5_2_two (Ψ := c'.Ψ) hΘ)
        ((isOrbifoldType_modelPull_iff c' hΘ.isFunctorial).2 ho)
        (pullTheta_comparison_modelPull c c' hΘ.isFunctorial)
    refine ⟨A, F, Φ, ΘA, hF, hΦ, hΘA, hoA, hmF, hmΦ, fun b => ?_⟩
    have h := congrFun (S.orbitMap_comparison c c') ((S.modelEP c.Ψ).X.π (F.obj b))
    exact h.symm.trans (congrArg (S.modelFunctor c'.Ψ).orbitMap (horb b))

end GCT.PolyfoldConstruction

end Polyfold
