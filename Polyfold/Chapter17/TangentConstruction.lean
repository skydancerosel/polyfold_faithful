import Polyfold.Chapter17.TangentModel

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.2 (pp. 781–784): the tangent uniformizers `TΨ` as local uniformizers of `TC`, the polyfold
structure `(TF, M)` and **Theorem 17.2.17**.  Numbers and pages are the 2021 text's.

# The polyfold structure of the tangent category

## The text, paraphrased

(pp. 781–783) `P : M(TΨ, TΨ') → M(Ψ, Ψ')¹` is a bundle, `TΨ : G ⋉ TO → TC` covers
`Ψ¹ : G ⋉ O¹ → C¹`, is fibrewise a topological linear isomorphism, and `|TΨ|` is a homeomorphism onto
an open set.  `TF(α)` is the set of the `TΨ`, `Ψ ∈ F(α)`; `(TF, M)` is a construction for
`TC → C¹` with a polyfold bundle structure, and `TF_P := TF ∘ P` the polyfold structure of the
GCT `TC`.  (**Theorem 17.2.17**, p. 783) For a GCT `C` with a polyfold structure `(F, M)` there is a
natural construction of the tangent category `TC` and a simultaneous polyfold structure for
`P : TC → C¹`, denoted `(TF, M)`.

## What is formalized (namespace `Polyfold.GCT.PolyfoldConstruction`)

* `tangentUnif hU Ψ hc` (**`TΨ` as a local uniformizer of the GCT `TC`**, for `Ψ̂` continuous):
  `tangentUnifFunctor_full`, `_faithful`, `tangentUnif_exists_smul`,
  `isOpenEmbedding_tangentUnifFunctor` (`|TΨ|` is an open embedding, through the model with `Ψ`
  adjoined).
* `tangentF` (`TF(β) = {TΨ | Ψ ∈ F(P(β))}`), `tangentUnif_isAt`, `tangentData`, the casts
  `tangentTopOf`, …, `tangentMulOf`, and **`tangentConstruction hU hcont`**, the polyfold structure
  of Definition 17.1.8 on `TC`, with `M(TΨ, TΨ')` the M-polyfold of Proposition 17.2.15;
  `tangentConstruction_hasUniformizers`.
* The bundle `P : TC → C¹`: `tangentCatProj_tangentUnifObj`, `tangentCatProj_tangentUnifMor`
  (`P ∘ TΨ = Ψ¹ ∘ (Id ⋉ τ)`), `tangentCatObjEquiv_tangentUnifObj` (fibrewise `TΨ = S_Ψ⁻¹`, a
  continuous linear isomorphism), `tangentTrBundleProj`, `isScSmoothMap_tangentTrBundleProj`,
  `tangentTrBundleProj_spec` (`M(TΨ, TΨ') → M(Ψ¹, Ψ'¹)` sc-smooth, compatible with `s`, `t`, `φ`).
* **`theorem_17_2_17_hyp`**, with the witness `reflection_continuous_hat_all`,
  `reflectionTangentConstruction`, `reflection_theorem_17_2_17`.

## Readings

* **The hypothesis `hcont`**: every `Ψ̂ : G × O → M(Ψ, Ψ)` is continuous.  Under it `TΨ` is a functor
  (Lemma 17.2.10 needs it; `lemma_17_2_10_of_continuous`, and `not_lemma_17_2_10` in
  `TangentUnifExamples.lean` for the general case), so `TΨ` is a local uniformizer.  It holds for the
  reflection witness (`reflection_continuous_hat_all`) and whenever Lemma 17.1.9 holds.
* **"Polyfold bundle"** is read as: the polyfold structure `(TF, M)` on `TC` together with
  `(F¹, M_{F¹})` on `C¹` (Theorem 17.1.28), related by `P` (`tangentCatProj`) so that
  `P ∘ TΨ = Ψ¹ ∘ (Id ⋉ τ)`, `TΨ` is fibrewise a continuous linear isomorphism onto `T_αC`, the maps
  `M(TΨ, TΨ') → M(Ψ¹, Ψ'¹)` are sc-smooth and compatible with the structure maps, and `|P|` is
  continuous.  Part III's strong bundles over ep-groupoids are not used: `TC → C¹` is a tangent
  bundle (no double filtration).
* `TF(β)` is indexed by `β ∈ TC` through `P(β)`: this is the text's `TF_P = TF ∘ P`; the text's
  `TF` on `C¹` is the same family read on `P(β)`.  `M(L, L')` uses the uniformizer
  `Ψ = tangentData L` chosen with `L = TΨ` (as Theorem 17.1.28's `levelOneData`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} {S : C.PolyfoldConstruction}

/-! ### The tangent uniformizers `TΨ : G ⋉ TO → TC` -/

section TangentUnif

variable (hU : S.HasUniformizers) (Ψ : S.Unif)

/-- Fullness of `TΨ` on objects: an isomorphism `TΨ(k) → TΨ(k')` of `TC` is `TΨ(g, k)` with
`g ∗ k = k'` (`Ψ̂` continuous). -/
theorem tangentUnif_exists_smul (hc : Continuous (S.hat Ψ)) {k k' : Ψ.1.P.TangentSpace}
    {ψ : S.TangentCatMor} (hs : ψ.src = S.tangentUnifObj hU Ψ k)
    (ht : ψ.tgt = S.tangentUnifObj hU Ψ k') :
    ∃ g : ULift.{1} Ψ.1.G, g • k = k' ∧ S.tangentUnifMor hU Ψ (g, k) = ψ := by
  have hs' : C.toGroupoidStr.src ψ.mor = Ψ.1.obj (basePt Ψ k) :=
    ψ.src_eq.trans (congrArg TangentCatObj.base hs)
  have ht' : C.toGroupoidStr.tgt ψ.mor = Ψ.1.obj (basePt Ψ k') :=
    congrArg TangentCatObj.base ht
  obtain ⟨g, -, hgm⟩ := Ψ.1.toUniformizer.exists_smul_eq_mor hs' ht'
  have hmor : S.tangentUnifMor hU Ψ (ULift.up g, k) = ψ :=
    TangentCatMor.ext' hs.symm hgm
  refine ⟨ULift.up g, injective_tangentUnifObj hU Ψ ?_, hmor⟩
  exact (tangentUnifMor_tgt_of_continuous hU Ψ hc (ULift.up g, k)).symm.trans
    ((congrArg TangentCatMor.tgt hmor).trans ht)

theorem tangentUnifFunctor_full (hc : Continuous (S.hat Ψ)) :
    (S.tangentUnifFunctor hU Ψ hc).toFunctor.Full := by
  refine (GroupoidFunctor.full_iff _).2 fun k k' ψ hs ht => ?_
  obtain ⟨g, hg, hm⟩ := tangentUnif_exists_smul hU Ψ hc hs ht
  exact ⟨(g, k), rfl, hg, hm⟩

theorem tangentUnifFunctor_faithful (hc : Continuous (S.hat Ψ)) :
    (S.tangentUnifFunctor hU Ψ hc).toFunctor.Faithful := by
  refine (GroupoidFunctor.faithful_iff _).2 fun φ φ' hs ht he => ?_
  obtain ⟨g, k⟩ := φ
  obtain ⟨g', k'⟩ := φ'
  change k = k' at hs
  subst hs
  change g • k = g' • k at ht
  have hm : Ψ.1.mor (g.down, basePt Ψ k) = Ψ.1.mor (g'.down, basePt Ψ k) :=
    congrArg TangentCatMor.mor he
  have hq : g.down • basePt Ψ k = g'.down • basePt Ψ k := by
    rw [← basePt_smul, ← basePt_smul, ht]
  have := (GroupoidFunctor.faithful_iff _).1 Ψ.1.faithful (g.down, basePt Ψ k)
    (g'.down, basePt Ψ k) rfl hq hm
  have hg : g = g' := ULift.ext _ _ (congrArg Prod.fst this)
  rw [hg]

/-- `|TΨ| ∘ π = |TΓ_Ψ'| ∘ π ∘ T(Sigma.mk none)` for the covering family `Ψ'` with `Ψ` adjoined. -/
theorem tangentUnif_orbitMap_π (hc : Continuous (S.hat Ψ)) (k : Ψ.1.P.TangentSpace) :
    (S.tangentUnifFunctor hU Ψ hc).orbitMap ((S.tangentTranslation Ψ).π k) =
      (S.tangentModelFunctor hU ((S.tangentCover hU).adjoin S Ψ).Ψ).orbitMap
        ((S.modelEpGroupoid ((S.tangentCover hU).adjoin S Ψ).Ψ).tangentEpGroupoid.π
          (modelTObjMk ((S.tangentCover hU).adjoin S Ψ).Ψ none k)) :=
  congrArg S.tangentCatGroupoid.π (tangentModelObj_mk hU (Ψ := ((S.tangentCover hU).adjoin S Ψ).Ψ)
    none k).symm

/-- **`|TΨ| : |G ⋉ TO| → |TC|` is an open embedding** (p. 783: "passing to orbit spaces `|TΨ|`
becomes a homeomorphism onto an open set"). -/
theorem isOpenEmbedding_tangentUnifFunctor (hc : Continuous (S.hat Ψ)) :
    @IsOpenEmbedding _ _ _ (S.tangentOrbitTopology hU) (S.tangentUnifFunctor hU Ψ hc).orbitMap := by
  let _ := S.tangentOrbitTopology hU
  set c := (S.tangentCover hU).adjoin S Ψ
  have hΓ := S.isHomeomorph_tangentModelOrbitEquiv hU c
  have hX := (S.modelEpGroupoid c.Ψ).tangentEpGroupoid.proposition_7_1_8_isOpenQuotientMap
  have hι : IsLocalHomeomorph (modelTObjMk c.Ψ none) :=
    (MPolyfold.isLocalScDiffeo_sigmaMk (fun i => (c.Ψ i).1.P) none).isLocalHomeomorph_tangentMap
  have hfac : (S.tangentUnifFunctor hU Ψ hc).orbitMap ∘ (S.tangentTranslation Ψ).π =
      (S.tangentModelFunctor hU c.Ψ).orbitMap ∘
        (S.modelEpGroupoid c.Ψ).tangentEpGroupoid.π ∘ modelTObjMk c.Ψ none :=
    funext fun k => S.tangentUnif_orbitMap_π hU Ψ hc k
  have hcomp : Continuous ((S.tangentModelFunctor hU c.Ψ).orbitMap ∘
      (S.modelEpGroupoid c.Ψ).tangentEpGroupoid.π ∘ modelTObjMk c.Ψ none) :=
    hΓ.continuous.comp (hX.continuous.comp hι.continuous)
  have hq : IsQuotientMap (S.tangentTranslation Ψ).π := isQuotientMap_quotient_mk'
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_
  · exact hq.continuous_iff.2 (hfac ▸ hcomp)
  · intro a b h
    induction a using Quotient.inductionOn with | h k => ?_
    induction b using Quotient.inductionOn with | h k' => ?_
    have h' : S.tangentCatGroupoid.π (S.tangentUnifObj hU Ψ k) =
        S.tangentCatGroupoid.π (S.tangentUnifObj hU Ψ k') := h
    obtain ⟨ψ, hs, ht⟩ := (S.tangentCatGroupoid.π_eq_π_iff).1 h'
    obtain ⟨g, hg, -⟩ := tangentUnif_exists_smul hU Ψ hc hs ht
    exact ((S.tangentTranslation Ψ).π_eq_π_iff).2 ⟨(g, k), rfl, hg⟩
  · intro W hW
    have hW' : (S.tangentUnifFunctor hU Ψ hc).orbitMap '' W =
        ((S.tangentModelFunctor hU c.Ψ).orbitMap ∘
          (S.modelEpGroupoid c.Ψ).tangentEpGroupoid.π ∘ modelTObjMk c.Ψ none) '' ((S.tangentTranslation Ψ).π ⁻¹' W) := by
      rw [← hfac]
      exact ((Set.image_comp _ _ _).trans
        (congrArg (fun V => (S.tangentUnifFunctor hU Ψ hc).orbitMap '' V)
          (image_preimage_eq W hq.surjective))).symm
    rw [hW']
    exact (hΓ.isOpenMap.comp (hX.isOpenMap.comp hι.isOpenMap)) _ (hW.preimage hq.continuous)

/-- **The tangent uniformizer `TΨ : G ⋉ TO → TC`** (2021 (17.35)–(17.40), p. 783) as a local
uniformizer of the GCT `TC` (`Ψ̂` continuous): the M-polyfold `TO`, the group `G` (lifted) acting
by `g ∗ h = T(g ∗ ·)(h)`, the functor of Lemma 17.2.10. -/
def tangentUnif (hc : Continuous (S.hat Ψ)) : (S.tangentGCT hU).LocalUniformizer where
  O := Ψ.1.P.TangentSpace
  P := Ψ.1.P.tangentPolyfold
  G := ULift.{1} Ψ.1.G
  smooth_smul g := MPolyfold.tangentMap_isScSmooth (Ψ.1.smooth_smul g.down)
  functor := S.tangentUnifFunctor hU Ψ hc
  injective_obj := injective_tangentUnifObj hU Ψ
  full := tangentUnifFunctor_full hU Ψ hc
  faithful := tangentUnifFunctor_faithful hU Ψ hc
  isOpenEmbedding_orbitMap := S.isOpenEmbedding_tangentUnifFunctor hU Ψ hc

end TangentUnif

/-! ### The polyfold structure `(TF, M)` of `TC` -/

section Construction

variable (hU : S.HasUniformizers) (hcont : ∀ Ψ : S.Unif, Continuous (S.hat Ψ))

/-- **`TF(β)`** (p. 783): the tangent uniformizers `TΨ` of the `Ψ ∈ F(P(β))`. -/
def tangentF (β : (S.tangentGCT hU).Obj) : Set (S.tangentGCT hU).LocalUniformizer :=
  {L | ∃ Ψ : S.Unif, Ψ.1 ∈ S.F (show S.TangentCatObj from β).base ∧
    L = S.tangentUnif hU Ψ (hcont Ψ)}

/-- `TΨ` is at `β` when `Ψ ∈ F(P(β))`. -/
theorem tangentUnif_isAt {β : (S.tangentGCT hU).Obj} {Ψ : S.Unif}
    (hΨ : Ψ.1 ∈ S.F (show S.TangentCatObj from β).base) :
    (S.tangentUnif hU Ψ (hcont Ψ)).IsAt β := by
  obtain ⟨q, hq⟩ := S.isAt _ Ψ.1 hΨ
  obtain ⟨k, -, hk⟩ := exists_tangentUnifObj_eq hU Ψ β q hq
  exact ⟨k, hk⟩

theorem exists_tangentData (L : GCT.Unif (S.tangentF hU hcont)) :
    ∃ Ψ : S.Unif, L.1 = S.tangentUnif hU Ψ (hcont Ψ) := by
  obtain ⟨L, β, Ψ, -, rfl⟩ := L
  exact ⟨Ψ, rfl⟩

/-- The uniformizer `Ψ ∈ F` chosen for `L ∈ TF` with `L = TΨ`. -/
def tangentData (L : GCT.Unif (S.tangentF hU hcont)) : S.Unif :=
  (S.exists_tangentData hU hcont L).choose

theorem tangentData_eq (L : GCT.Unif (S.tangentF hU hcont)) :
    L.1 = S.tangentUnif hU (S.tangentData hU hcont L) (hcont _) :=
  (S.exists_tangentData hU hcont L).choose_spec

/-- The topology of `M(L, L')` for `L = TΨ`, `L' = TΨ'`. -/
@[instance_reducible]
def tangentTopOf : ∀ (L L' : (S.tangentGCT hU).LocalUniformizer) (Ψ Ψ' : S.Unif),
    L = S.tangentUnif hU Ψ (hcont Ψ) → L' = S.tangentUnif hU Ψ' (hcont Ψ') →
      TopologicalSpace (L.Trans L')
  | _, _, Ψ, Ψ', rfl, rfl => (inferInstance : TopologicalSpace (S.TTrM hU Ψ Ψ'))

theorem tangentT2Of : ∀ (L L' : (S.tangentGCT hU).LocalUniformizer) (Ψ Ψ' : S.Unif)
    (h : L = S.tangentUnif hU Ψ (hcont Ψ)) (h' : L' = S.tangentUnif hU Ψ' (hcont Ψ')),
    @T2Space (L.Trans L') (S.tangentTopOf hU hcont L L' Ψ Ψ' h h')
  | _, _, Ψ, Ψ', rfl, rfl => (inferInstance : T2Space (S.TTrM hU Ψ Ψ'))

theorem tangentParaOf : ∀ (L L' : (S.tangentGCT hU).LocalUniformizer) (Ψ Ψ' : S.Unif)
    (h : L = S.tangentUnif hU Ψ (hcont Ψ)) (h' : L' = S.tangentUnif hU Ψ' (hcont Ψ')),
    @ParacompactSpace (L.Trans L') (S.tangentTopOf hU hcont L L' Ψ Ψ' h h')
  | _, _, Ψ, Ψ', rfl, rfl => (inferInstance : ParacompactSpace (S.TTrM hU Ψ Ψ'))

/-- The M-polyfold `M(L, L')` for `L = TΨ`, `L' = TΨ'`: Proposition 17.2.15's `tangentTrPolyfold`. -/
def tangentMOf : ∀ (L L' : (S.tangentGCT hU).LocalUniformizer) (Ψ Ψ' : S.Unif)
    (h : L = S.tangentUnif hU Ψ (hcont Ψ)) (h' : L' = S.tangentUnif hU Ψ' (hcont Ψ')),
    @MPolyfold (L.Trans L') (S.tangentTopOf hU hcont L L' Ψ Ψ' h h')
      (S.tangentT2Of hU hcont L L' Ψ Ψ' h h') (S.tangentParaOf hU hcont L L' Ψ Ψ' h h')
  | _, _, Ψ, Ψ', rfl, rfl => S.tangentTrPolyfold hU Ψ Ψ'

theorem tangentSrcOf : ∀ (L L' : (S.tangentGCT hU).LocalUniformizer) (Ψ Ψ' : S.Unif)
    (h : L = S.tangentUnif hU Ψ (hcont Ψ)) (h' : L' = S.tangentUnif hU Ψ' (hcont Ψ')),
    letI := S.tangentTopOf hU hcont L L' Ψ Ψ' h h'
    letI := S.tangentT2Of hU hcont L L' Ψ Ψ' h h'
    letI := S.tangentParaOf hU hcont L L' Ψ Ψ' h h'
    (S.tangentMOf hU hcont L L' Ψ Ψ' h h').IsLocalScDiffeo L.P GroupoidStr.TransitionSet.src
  | _, _, _, _, rfl, rfl => tangentTr_isLocalScDiffeo_src

theorem tangentTgtOf : ∀ (L L' : (S.tangentGCT hU).LocalUniformizer) (Ψ Ψ' : S.Unif)
    (h : L = S.tangentUnif hU Ψ (hcont Ψ)) (h' : L' = S.tangentUnif hU Ψ' (hcont Ψ')),
    letI := S.tangentTopOf hU hcont L L' Ψ Ψ' h h'
    letI := S.tangentT2Of hU hcont L L' Ψ Ψ' h h'
    letI := S.tangentParaOf hU hcont L L' Ψ Ψ' h h'
    (S.tangentMOf hU hcont L L' Ψ Ψ' h h').IsLocalScDiffeo L'.P GroupoidStr.TransitionSet.tgt
  | _, _, _, _, rfl, rfl => tangentTr_isLocalScDiffeo_tgt

theorem tangentUnitOf : ∀ (L : (S.tangentGCT hU).LocalUniformizer) (Ψ : S.Unif)
    (h : L = S.tangentUnif hU Ψ (hcont Ψ)),
    letI := S.tangentTopOf hU hcont L L Ψ Ψ h h
    letI := S.tangentT2Of hU hcont L L Ψ Ψ h h
    letI := S.tangentParaOf hU hcont L L Ψ Ψ h h
    L.P.IsScSmoothMap (S.tangentMOf hU hcont L L Ψ Ψ h h) GroupoidStr.TransitionSet.unit
  | _, Ψ, rfl => tangentTr_isScSmoothMap_unit Ψ

theorem tangentInvOf : ∀ (L L' : (S.tangentGCT hU).LocalUniformizer) (Ψ Ψ' : S.Unif)
    (h : L = S.tangentUnif hU Ψ (hcont Ψ)) (h' : L' = S.tangentUnif hU Ψ' (hcont Ψ')),
    letI := S.tangentTopOf hU hcont L L' Ψ Ψ' h h'
    letI := S.tangentT2Of hU hcont L L' Ψ Ψ' h h'
    letI := S.tangentParaOf hU hcont L L' Ψ Ψ' h h'
    letI := S.tangentTopOf hU hcont L' L Ψ' Ψ h' h
    letI := S.tangentT2Of hU hcont L' L Ψ' Ψ h' h
    letI := S.tangentParaOf hU hcont L' L Ψ' Ψ h' h
    (S.tangentMOf hU hcont L L' Ψ Ψ' h h').IsScSmoothMap (S.tangentMOf hU hcont L' L Ψ' Ψ h' h)
      GroupoidStr.TransitionSet.inv
  | _, _, _, _, rfl, rfl => tangentTr_isScSmoothMap_inv

theorem tangentMulOf : ∀ (L L' L'' : (S.tangentGCT hU).LocalUniformizer) (Ψ Ψ' Ψ'' : S.Unif)
    (h : L = S.tangentUnif hU Ψ (hcont Ψ)) (h' : L' = S.tangentUnif hU Ψ' (hcont Ψ'))
    (h'' : L'' = S.tangentUnif hU Ψ'' (hcont Ψ'')),
    letI := S.tangentTopOf hU hcont L' L'' Ψ' Ψ'' h' h''
    letI := S.tangentT2Of hU hcont L' L'' Ψ' Ψ'' h' h''
    letI := S.tangentParaOf hU hcont L' L'' Ψ' Ψ'' h' h''
    letI := S.tangentTopOf hU hcont L L' Ψ Ψ' h h'
    letI := S.tangentT2Of hU hcont L L' Ψ Ψ' h h'
    letI := S.tangentParaOf hU hcont L L' Ψ Ψ' h h'
    letI := S.tangentTopOf hU hcont L L'' Ψ Ψ'' h h''
    letI := S.tangentT2Of hU hcont L L'' Ψ Ψ'' h h''
    letI := S.tangentParaOf hU hcont L L'' Ψ Ψ'' h h''
    MPolyfold.IsScSmoothOnFibredProduct (S.tangentMOf hU hcont L' L'' Ψ' Ψ'' h' h'')
      (S.tangentMOf hU hcont L L' Ψ Ψ' h h') (S.tangentMOf hU hcont L L'' Ψ Ψ'' h h'')
      (S.tangentSrcOf hU hcont L' L'' Ψ' Ψ'' h' h'')
      (S.tangentTgtOf hU hcont L L' Ψ Ψ' h h').isScSmoothMap GroupoidStr.TransitionSet.mul
  | _, _, _, _, _, _, rfl, rfl, rfl => tangentTr_isScSmoothMap_mul

/-- **2021 Theorem 17.2.17, p. 783, the polyfold structure `(TF, M)` on `TC`**: `TF(β)` consists of
the tangent uniformizers `TΨ : G ⋉ TO → TC` of the `Ψ ∈ F(P(β))`, and `M(TΨ, TΨ')` carries the
natural M-polyfold structure of Proposition 17.2.15 (for the chosen `Ψ = tangentData L` with
`L = TΨ`). -/
def tangentConstruction : (S.tangentGCT hU).PolyfoldConstruction where
  F := S.tangentF hU hcont
  isAt β L hL := by
    obtain ⟨Ψ, hΨ, rfl⟩ := hL
    exact tangentUnif_isAt hU hcont hΨ
  topM L L' := S.tangentTopOf hU hcont L.1 L'.1 (S.tangentData hU hcont L)
    (S.tangentData hU hcont L') (S.tangentData_eq hU hcont L) (S.tangentData_eq hU hcont L')
  t2M L L' := S.tangentT2Of hU hcont L.1 L'.1 (S.tangentData hU hcont L)
    (S.tangentData hU hcont L') (S.tangentData_eq hU hcont L) (S.tangentData_eq hU hcont L')
  paraM L L' := S.tangentParaOf hU hcont L.1 L'.1 (S.tangentData hU hcont L)
    (S.tangentData hU hcont L') (S.tangentData_eq hU hcont L) (S.tangentData_eq hU hcont L')
  M L L' := S.tangentMOf hU hcont L.1 L'.1 (S.tangentData hU hcont L)
    (S.tangentData hU hcont L') (S.tangentData_eq hU hcont L) (S.tangentData_eq hU hcont L')
  isLocalScDiffeo_src L L' := S.tangentSrcOf hU hcont L.1 L'.1 (S.tangentData hU hcont L)
    (S.tangentData hU hcont L') (S.tangentData_eq hU hcont L) (S.tangentData_eq hU hcont L')
  isLocalScDiffeo_tgt L L' := S.tangentTgtOf hU hcont L.1 L'.1 (S.tangentData hU hcont L)
    (S.tangentData hU hcont L') (S.tangentData_eq hU hcont L) (S.tangentData_eq hU hcont L')
  isScSmoothMap_unit L := S.tangentUnitOf hU hcont L.1 (S.tangentData hU hcont L)
    (S.tangentData_eq hU hcont L)
  isScSmoothMap_inv L L' := S.tangentInvOf hU hcont L.1 L'.1 (S.tangentData hU hcont L)
    (S.tangentData hU hcont L') (S.tangentData_eq hU hcont L) (S.tangentData_eq hU hcont L')
  isScSmoothMap_mul L L' L'' := S.tangentMulOf hU hcont L.1 L'.1 L''.1 (S.tangentData hU hcont L)
    (S.tangentData hU hcont L') (S.tangentData hU hcont L'') (S.tangentData_eq hU hcont L)
    (S.tangentData_eq hU hcont L') (S.tangentData_eq hU hcont L'')

theorem tangentConstruction_hasUniformizers :
    (S.tangentConstruction hU hcont).HasUniformizers := fun β => by
  obtain ⟨L, hL⟩ := hU (show S.TangentCatObj from β).base
  have hα : ∃ α, L ∈ S.F α := ⟨_, hL⟩
  exact ⟨S.tangentUnif hU ⟨L, hα⟩ (hcont _), ⟨L, hα⟩, hL, rfl⟩

end Construction

/-! ### The bundle `P : TC → C¹` -/

section Bundle

variable (hU : S.HasUniformizers)

/-- **`P ∘ TΨ = Ψ¹ ∘ (Id ⋉ τ)` on objects** (the square on p. 783). -/
theorem tangentCatProj_tangentUnifObj (Ψ : S.Unif) (k : Ψ.1.P.TangentSpace) :
    S.tangentCatProj.obj (S.tangentUnifObj hU Ψ k) =
      (S.levelOneFunctor Ψ).obj (Ψ.1.P.tangentProj k) := rfl

/-- **`P ∘ TΨ = Ψ¹ ∘ (Id ⋉ τ)` on morphisms**: `P(TΨ(g, h)) = Ψ¹(g, τ(h))`. -/
theorem tangentCatProj_tangentUnifMor (Ψ : S.Unif) (p : ULift.{1} Ψ.1.G × Ψ.1.P.TangentSpace) :
    S.tangentCatProj.mor (S.tangentUnifMor hU Ψ p) =
      (S.levelOneFunctor Ψ).mor (p.1.down, Ψ.1.P.tangentProj p.2) := rfl

/-- **`TΨ` is fibrewise a topological linear isomorphism** (p. 783): on the fibre `T_xO`,
`TΨ` is the inverse of the chart `S_Ψ : T_{Ψ(x)}C ≃L T_xO` of Proposition 17.2.4, through the
identification `TC ≃ ⊔_α T_αC` of Definition 17.2.6. -/
theorem tangentCatObjEquiv_tangentUnifObj (Ψ : S.Unif) (k : Ψ.1.P.TangentSpace) :
    haveI : Fact (S.TangentObj (Ψ.1.obj (basePt Ψ k))) := ⟨tangentObj_of_unif hU Ψ k⟩
    S.tangentCatObjEquiv (S.tangentUnifObj hU Ψ k) =
      ⟨Ψ.1.obj (basePt Ψ k), (S.tangentChartCLE (Ψ.1.obj (basePt Ψ k)) Ψ (Ψ.1.P.tangentProj k)
        rfl).symm ⟨k, rfl⟩⟩ := by
  have : Fact (S.TangentObj (Ψ.1.obj (basePt Ψ k))) := ⟨tangentObj_of_unif hU Ψ k⟩
  have key : S.tangentChartCLE (Ψ.1.obj (basePt Ψ k)) Ψ (Ψ.1.P.tangentProj k) rfl
      ((S.refChart (tangentObj_of_unif hU Ψ k)).symm (S.tangentUnifObj hU Ψ k).vec) = ⟨k, rfl⟩ := by
    refine Subtype.ext ((transTangent_apply _ rfl rfl _).trans ?_)
    change S.transMap _ ((S.refChart _) ((S.refChart _).symm _)).1 = k
    erw [Equiv.apply_symm_apply]
    exact (transMap_unitTr_comp _ _ _ _ _ _ rfl).trans (transMap_unitTr_self _ _ rfl)
  have h2 := congrArg (S.tangentChartCLE (Ψ.1.obj (basePt Ψ k)) Ψ (Ψ.1.P.tangentProj k) rfl).symm key
  rw [ContinuousLinearEquiv.symm_apply_apply] at h2
  exact congrArg (Sigma.mk (β := S.TangentSpaceAt) (Ψ.1.obj (basePt Ψ k))) h2

variable (hc : S.HasCoveringUniformizers)

/-- **The bundle projection `M(TΨ, TΨ') → M(Ψ¹, Ψ'¹)`** (p. 783): `x ↦ p(x)` read in
`M(Ψ, Ψ')¹ = M(Ψ¹, Ψ'¹)` (Theorem 17.1.28). -/
def tangentTrBundleProj {Ψ Ψ' : S.Unif} (x : S.TTrM hU Ψ Ψ') : S.LTr hc Ψ Ψ' :=
  (S.ltrHomeomorph hc Ψ Ψ').symm (tangentTrProj hU x)

theorem ltrHomeomorph_tangentTrBundleProj {Ψ Ψ' : S.Unif} (x : S.TTrM hU Ψ Ψ') :
    S.ltrHomeomorph hc Ψ Ψ' (S.tangentTrBundleProj hU hc x) = tangentTrProj hU x :=
  (S.ltrHomeomorph hc Ψ Ψ').apply_symm_apply _

/-- **`M(TΨ, TΨ') → M(Ψ¹, Ψ'¹)` is sc-smooth.** -/
theorem isScSmoothMap_tangentTrBundleProj (Ψ Ψ' : S.Unif) :
    (S.tangentTrPolyfold hU Ψ Ψ').IsScSmoothMap (S.ltrPolyfold hc Ψ Ψ')
      (S.tangentTrBundleProj hU hc (Ψ := Ψ) (Ψ' := Ψ')) :=
  (S.ltr_isScSmoothMap_homeomorph_symm hc Ψ Ψ').comp isScSmoothMap_tangentTrProj

/-- The bundle projection commutes with `s`, `t` and keeps the morphism of `C`. -/
theorem tangentTrBundleProj_spec {Ψ Ψ' : S.Unif} (x : S.TTrM hU Ψ Ψ') :
    (S.tangentTrBundleProj hU hc x).src = Ψ.1.P.tangentProj x.src ∧
      (S.tangentTrBundleProj hU hc x).tgt = Ψ'.1.P.tangentProj x.tgt ∧
      (S.tangentTrBundleProj hU hc x).mor.1 = x.mor.mor := by
  exact ⟨MPolyfold.level_ext (tangentTrProj_src x), MPolyfold.level_ext (tangentTrProj_tgt x),
    tangentTrProj_mor x⟩

end Bundle

/-! ### Theorem 17.2.17 -/

/-- **2021 Theorem 17.2.17, p. 783** (with the hypothesis `hcont`: every `Ψ̂` is continuous, under
which `TΨ` is a functor, Lemma 17.2.10): for a polyfold structure `(F, M)` on `C` with
`F(α) ≠ ∅`, the tangent category `TC` is a GCT (Proposition 17.2.16) and carries the polyfold
structure `(TF, M)` (`tangentConstruction`), `TF(β) = {TΨ | Ψ ∈ F(P(β))}`, with `TF(β) ≠ ∅`; and
`P : TC → C¹` is a polyfold bundle in the reading of the module docstring: `P ∘ TΨ = Ψ¹ ∘ (Id ⋉ τ)`
on objects and morphisms, `TΨ` is fibrewise the inverse of the continuous linear chart
`S_Ψ : T_{Ψ(x)}C ≃L T_xO`, the bundle projections `M(TΨ, TΨ') → M(Ψ¹, Ψ'¹)` are sc-smooth and
compatible with `s`, `t` and the morphisms, and `|P| : |TC| → |C¹|` is continuous. -/
theorem theorem_17_2_17_hyp (hU : S.HasUniformizers)
    (hcont : ∀ Ψ : S.Unif, Continuous (S.hat Ψ)) :
    (S.tangentGCT hU).toGroupoidStr = S.tangentCatGroupoid ∧
    (S.tangentConstruction hU hcont).HasUniformizers ∧
    (∀ β L, L ∈ (S.tangentConstruction hU hcont).F β ↔
      ∃ Ψ : S.Unif, Ψ.1 ∈ S.F (show S.TangentCatObj from β).base ∧
        L = S.tangentUnif hU Ψ (hcont Ψ)) ∧
    (∀ (Ψ : S.Unif) k, S.tangentCatProj.obj ((S.tangentUnif hU Ψ (hcont Ψ)).obj k) =
      (S.levelOneFunctor Ψ).obj (Ψ.1.P.tangentProj k)) ∧
    (∀ (Ψ : S.Unif) (p : ULift.{1} Ψ.1.G × Ψ.1.P.TangentSpace),
      S.tangentCatProj.mor ((S.tangentUnif hU Ψ (hcont Ψ)).mor p) =
        (S.levelOneFunctor Ψ).mor (p.1.down, Ψ.1.P.tangentProj p.2)) ∧
    (∀ (Ψ : S.Unif) (k : Ψ.1.P.TangentSpace),
      haveI : Fact (S.TangentObj (Ψ.1.obj (basePt Ψ k))) := ⟨tangentObj_of_unif hU Ψ k⟩
      S.tangentCatObjEquiv ((S.tangentUnif hU Ψ (hcont Ψ)).obj k) =
        ⟨Ψ.1.obj (basePt Ψ k), (S.tangentChartCLE (Ψ.1.obj (basePt Ψ k)) Ψ
          (Ψ.1.P.tangentProj k) rfl).symm ⟨k, rfl⟩⟩) ∧
    (∀ Ψ Ψ' : S.Unif, (S.tangentTrPolyfold hU Ψ Ψ').IsScSmoothMap
      (S.ltrPolyfold (S.hasCoveringUniformizers_of_hasUniformizers hU) Ψ Ψ')
      (S.tangentTrBundleProj hU (S.hasCoveringUniformizers_of_hasUniformizers hU)
        (Ψ := Ψ) (Ψ' := Ψ'))) ∧
    (∀ (Ψ Ψ' : S.Unif) (x : S.TTrM hU Ψ Ψ'),
      (S.tangentTrBundleProj hU (S.hasCoveringUniformizers_of_hasUniformizers hU) x).src =
          Ψ.1.P.tangentProj x.src ∧
        (S.tangentTrBundleProj hU (S.hasCoveringUniformizers_of_hasUniformizers hU) x).tgt =
          Ψ'.1.P.tangentProj x.tgt ∧
        (S.tangentTrBundleProj hU (S.hasCoveringUniformizers_of_hasUniformizers hU) x).mor.1 =
          x.mor.mor) ∧
    @Continuous _ _ (S.tangentOrbitTopology hU)
      (S.levelOneTopology (S.hasCoveringUniformizers_of_hasUniformizers hU))
      S.tangentCatProj.orbitMap :=
  ⟨rfl, S.tangentConstruction_hasUniformizers hU hcont, fun _ _ => Iff.rfl,
    fun Ψ k => tangentCatProj_tangentUnifObj hU Ψ k,
    fun Ψ p => tangentCatProj_tangentUnifMor hU Ψ p,
    fun Ψ k => tangentCatObjEquiv_tangentUnifObj hU Ψ k,
    fun Ψ Ψ' => S.isScSmoothMap_tangentTrBundleProj hU _ Ψ Ψ',
    fun _ _ x => S.tangentTrBundleProj_spec hU _ x,
    S.continuous_orbitMap_tangentCatProj hU⟩

/-! ### The witness of `hcont` -/

/-- **Every `Ψ̂` of the reflection witness is continuous** (`ℤ/2` acting on `ℝ` by `x ↦ -x`,
the untwisted construction): the hypothesis `hcont` of `theorem_17_2_17_hyp` is satisfiable,
with a uniformizer whose group acts non-trivially. -/
theorem reflection_continuous_hat_all :
    ∀ Ψ : reflectionConstruction.Unif, Continuous (reflectionConstruction.hat Ψ) := by
  rintro ⟨L, x, hL⟩
  obtain rfl : L = _ := hL
  exact twist_continuous_hat _ _ x continuous_id

/-- **The tangent construction of the reflection witness.** -/
def reflectionTangentConstruction :
    (reflectionConstruction.tangentGCT reflectionConstruction_hasUniformizers).PolyfoldConstruction :=
  reflectionConstruction.tangentConstruction reflectionConstruction_hasUniformizers
    reflection_continuous_hat_all

theorem reflectionTangentConstruction_hasUniformizers :
    reflectionTangentConstruction.HasUniformizers :=
  reflectionConstruction.tangentConstruction_hasUniformizers _ _

/-- **`theorem_17_2_17_hyp` for the reflection witness.** -/
theorem reflection_theorem_17_2_17 :
    (reflectionConstruction.tangentGCT reflectionConstruction_hasUniformizers).toGroupoidStr =
      reflectionConstruction.tangentCatGroupoid ∧
    reflectionTangentConstruction.HasUniformizers :=
  ⟨rfl, reflectionTangentConstruction_hasUniformizers⟩

end GCT.PolyfoldConstruction

end Polyfold
