import Polyfold.Chapter17.TangentConstruction
import Polyfold.Chapter17.TangentUnifExamples
import Polyfold.Chapter17.ModelExamples

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.2 (pp. 781–784): the model of the tangent polyfold structure `(TF, M)` of Theorem 17.2.17 and
the tangent `T(X_Ψ)` (Theorem 8.1.1) of the model of `C`.  Numbers and pages are the 2021 text's.

# The model `X^{TF}_Φ` and the tangent ep-groupoid `T(X_Ψ)`

## The text, paraphrased

(pp. 782–783) The topology of `|TC|` is defined through `TΓ : T(X_Ψ) → TC` (17.52); the tangent
uniformizers `TΨ : G ⋉ TO → TC` make up `TF`, with `M(TΨ, TΨ')` carrying the natural M-polyfold
structure of Proposition 17.2.15, and `(TF, M)` is the polyfold structure of `TC`
(Theorem 17.2.17: "this associates to a polyfold another one").  The text does not compare the
model `X^{TF}_Φ` of `TC` built from `TF` (17.7) with the tangent `T(X_Ψ)` of the model of `C`;
we read the construction as saying that the two agree, `Ψ_λ` the uniformizers with
`Φ_λ = TΨ_λ`, and prove it.

## What is formalized (namespace `Polyfold.GCT.PolyfoldConstruction`)

* `GroupoidFunctor.full_faithful_essSurj_of_bijective` (namespace `Polyfold`): a functor of
  groupoids bijective on objects and morphisms is full, faithful and essentially surjective.
* `tangentObjCast`, `tangentObjCast_spec` (`O_L = TO` for `L = TΨ`), `tangentTrCast`,
  `tangentTrCast_spec` (`M(L, L') = M(TΨ, TΨ')` for `L = TΨ`, `L' = TΨ'`).
* For a family `Φ : ι → TF` (`ι : Type u`, lifted to `ULift ι` by `tangentFamilyLift`, the universe
  of `TC`) and `Ψ = tangentFamilyData Φ = tangentData ∘ Φ` (`Φ_λ = TΨ_λ`):
  **`tangentModelIsoFunctor hU hcont Φ : X^{TF}_Φ → T(X_Ψ)`**, `(λ, h) ↦ T(Sigma.mk λ)(h)` on
  objects (`tmFunObj`) and `((λ, μ), a) ↦ T(Sigma.mk (λ, μ))(v)` on morphisms (`tmFunMor`),
  `v ∈ TM(Ψ_λ, Ψ_μ)` the vector of `a ∈ M(TΨ_λ, TΨ_μ)` (`tmTrVec`, through Proposition
  17.2.15's `tangentTrHomeomorph`).
* `bijective_tangentModelIsoFunctor_obj`, `_mor`, `isLocalScDiffeo_tangentModelIsoFunctor_obj`,
  `_mor` (an isomorphism of ep-groupoids); `tangentModelIsoFunctor_full`, `_faithful`,
  `_essSurj`, **`isEquivalence_tangentModelIsoFunctor`** (Definition 10.1.1, through Lemma 10.1.2),
  for every family `Φ`; `tangentModelFunctor_comp_tangentModelIsoFunctor_obj`, `_mor`,
  `orbitMap_tangentModelFunctor_comp_tangentModelIsoFunctor` (`TΓ_Ψ ∘ F = Γ^{TF}_Φ`, the triangle
  with `TC`); all collected in **`tangentModelIso_spec`**.
* `tangentZeroObj`, `tangentRefFamily`, `tangentRefCover`: the tangent uniformizers `TΨ_α` of the
  reference uniformizers `Ψ_α` of the objects `α` of `C¹` with `F(α) ≠ ∅`, a covering family of
  `TF` indexed in the universe of `C`; **`tangentModel_equivalence`**: on it, `F` is an
  equivalence, `X^{TF} → TC` is an equivalence with `|·|` a homeomorphism (Lemma 17.1.15 for
  `(TF, M)`), and `TΓ_Ψ : T(X_Ψ) → TC` is an equivalence of categories.
* The witness (reflection `ℤ/2 ⋉ ℝ`): `reflZeroTangent` (the zero vector of `T_0ℝ`),
  `tangentMap_neg_reflZeroTangent` (`T(y ↦ −y)` fixes it), `reflTangentUnif` (`TΨ₀ ∈ TF`),
  `reflectionTangentCover` (`(TΨ₀)` covers `|TC|`), `reflTangentAut`, and
  **`reflectionTangentFamily_isotropy`**: `F` is an equivalence, `X^{TF} → TC` is an equivalence,
  and `X^{TF}` has an automorphism `TΨ₀(−1, 0)` of `TΨ₀(0)` other than the unit, whose image in
  `T(X_Ψ)` is not the unit either.

## Readings

* The statement is in terms of the family `Ψ = tangentData ∘ Φ`: a uniformizer `L ∈ TF` is
  `TΨ` for some `Ψ ∈ F`, and `M(L, L')` of `tangentConstruction` is built from the chosen
  `Ψ = tangentData L` (`tangentData_eq`); `L` need not determine `Ψ`.  For a covering family `Φ`
  of `TF` the family `tangentData ∘ Φ` need not be a covering family of `C`: the objects of `TC`
  lie over `C_1` only (`TangentObj`), so the footprints of the `Ψ_λ` need only cover the image of
  `C_1` in `|C|`.  The equivalence `X^{TF}_Φ → T(X_Ψ)` holds for every family `Φ`, covering or
  not; it is an isomorphism of ep-groupoids.
* Indices: the model of `TF` has index type in the universe `max u 1` of `TC`, that of `F` in `u`;
  we take `Φ` indexed by `ι : Type u` and form `X^{TF}` on `ULift ι`.
* The functor is checked on morphisms through the faithful functor `TΓ_Ψ : T(X_Ψ) → TC`
  (Proposition 17.2.16): both sides have the same source, target and image in `TC`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

/-- A functor of groupoids bijective on objects and on morphisms is full, faithful and
essentially surjective. -/
theorem GroupoidFunctor.full_faithful_essSurj_of_bijective.{v, w} {Obj Mor : Type v}
    {Obj' Mor' : Type w}
    {G : GroupoidStr Obj Mor} {H : GroupoidStr Obj' Mor'} (F : GroupoidFunctor G H)
    (ho : Bijective F.obj) (hm : Bijective F.mor) :
    F.toFunctor.Full ∧ F.toFunctor.Faithful ∧ F.toFunctor.EssSurj := by
  refine ⟨(GroupoidFunctor.full_iff _).2 fun x x' ψ hs ht => ?_,
    (GroupoidFunctor.faithful_iff _).2 fun φ φ' _ _ he => hm.1 he,
    (GroupoidFunctor.essSurj_iff _).2 fun y => ?_⟩
  · obtain ⟨φ, rfl⟩ := hm.2 ψ
    exact ⟨φ, ho.1 ((F.src_mor φ).symm.trans hs), ho.1 ((F.tgt_mor φ).symm.trans ht), rfl⟩
  · obtain ⟨x, rfl⟩ := ho.2 y
    exact ⟨x, H.unit (F.obj x), H.src_unit _, H.tgt_unit _⟩

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} {S : C.PolyfoldConstruction}

/-! ### The casts along `L = TΨ` -/

section Casts

variable (hU : S.HasUniformizers) (hcont : ∀ Ψ : S.Unif, Continuous (S.hat Ψ))

/-- The identification `O_L = TO` of `L = TΨ`. -/
def tangentObjCast : ∀ (L : (S.tangentGCT hU).LocalUniformizer) (Ψ : S.Unif),
    L = S.tangentUnif hU Ψ (hcont Ψ) → L.O → Ψ.1.P.TangentSpace
  | _, _, rfl => id

/-- `O_L = TO` is bijective, a local sc-diffeomorphism `O_L → TO`, and `L = TΨ` on objects. -/
theorem tangentObjCast_spec : ∀ (L : (S.tangentGCT hU).LocalUniformizer) (Ψ : S.Unif)
    (h : L = S.tangentUnif hU Ψ (hcont Ψ)),
    Bijective (S.tangentObjCast hU hcont L Ψ h) ∧
      L.P.IsLocalScDiffeo Ψ.1.P.tangentPolyfold (S.tangentObjCast hU hcont L Ψ h) ∧
      ∀ x, (show S.TangentCatObj from L.obj x) =
        S.tangentUnifObj hU Ψ (S.tangentObjCast hU hcont L Ψ h x)
  | _, _, rfl => ⟨bijective_id, MPolyfold.isLocalScDiffeo_id, fun _ => rfl⟩

/-- The identification `M(L, L') = M(TΨ, TΨ')` of `L = TΨ`, `L' = TΨ'`. -/
def tangentTrCast : ∀ (L L' : (S.tangentGCT hU).LocalUniformizer) (Ψ Ψ' : S.Unif),
    L = S.tangentUnif hU Ψ (hcont Ψ) → L' = S.tangentUnif hU Ψ' (hcont Ψ') →
    L.Trans L' → S.TTrM hU Ψ Ψ'
  | _, _, _, _, rfl, rfl => id

/-- `M(L, L') = M(TΨ, TΨ')` is bijective, a local sc-diffeomorphism for the M-polyfold structure
of `tangentConstruction` and Proposition 17.2.15's, and keeps source, target and morphism. -/
theorem tangentTrCast_spec : ∀ (L L' : (S.tangentGCT hU).LocalUniformizer) (Ψ Ψ' : S.Unif)
    (h : L = S.tangentUnif hU Ψ (hcont Ψ)) (h' : L' = S.tangentUnif hU Ψ' (hcont Ψ')),
    letI := S.tangentTopOf hU hcont L L' Ψ Ψ' h h'
    letI := S.tangentT2Of hU hcont L L' Ψ Ψ' h h'
    letI := S.tangentParaOf hU hcont L L' Ψ Ψ' h h'
    Bijective (S.tangentTrCast hU hcont L L' Ψ Ψ' h h') ∧
      (S.tangentMOf hU hcont L L' Ψ Ψ' h h').IsLocalScDiffeo (S.tangentTrPolyfold hU Ψ Ψ')
        (S.tangentTrCast hU hcont L L' Ψ Ψ' h h') ∧
      ∀ a : L.Trans L',
        (S.tangentTrCast hU hcont L L' Ψ Ψ' h h' a).src = S.tangentObjCast hU hcont L Ψ h a.src ∧
        (S.tangentTrCast hU hcont L L' Ψ Ψ' h h' a).tgt =
          S.tangentObjCast hU hcont L' Ψ' h' a.tgt ∧
        (S.tangentTrCast hU hcont L L' Ψ Ψ' h h' a).mor = (show S.TangentCatMor from a.mor)
  | _, _, Ψ, Ψ', rfl, rfl =>
    ⟨bijective_id, MPolyfold.isLocalScDiffeo_id (P := S.tangentTrPolyfold hU Ψ Ψ'),
      fun _ => ⟨rfl, rfl, rfl⟩⟩

end Casts

/-! ### The functor `X^{TF}_Φ → T(X_Ψ)` -/

section ModelIso

variable (hU : S.HasUniformizers) (hcont : ∀ Ψ : S.Unif, Continuous (S.hat Ψ)) {ι : Type u}
  (Φ : ι → (S.tangentConstruction hU hcont).Unif)

/-- The family `Φ` of `TF` indexed by `ULift ι` (the universe of `TC`). -/
abbrev tangentFamilyLift : ULift.{1} ι → (S.tangentConstruction hU hcont).Unif :=
  fun i => Φ i.down

/-- **The family `Ψ = tangentData ∘ Φ` of `F`** (`Φ_λ = TΨ_λ`). -/
abbrev tangentFamilyData : ι → S.Unif := fun i => S.tangentData hU hcont (Φ i)

/-- `O_{Φ_λ} = TO_λ`. -/
abbrev tmObjCast (i : ι) : (Φ i).1.O → (S.tangentFamilyData hU hcont Φ i).1.P.TangentSpace :=
  S.tangentObjCast hU hcont (Φ i).1 _ (S.tangentData_eq hU hcont (Φ i))

/-- `M(Φ_λ, Φ_μ) = M(TΨ_λ, TΨ_μ)`. -/
abbrev tmTrCast (i j : ι) : (S.tangentConstruction hU hcont).Tr (Φ i) (Φ j) →
    S.TTrM hU (S.tangentFamilyData hU hcont Φ i) (S.tangentFamilyData hU hcont Φ j) :=
  S.tangentTrCast hU hcont (Φ i).1 (Φ j).1 _ _ (S.tangentData_eq hU hcont (Φ i))
    (S.tangentData_eq hU hcont (Φ j))

/-- `M(Φ_λ, Φ_μ) → TM(Ψ_λ, Ψ_μ)`: the cast followed by the inverse of Proposition 17.2.15's
identification `TM(Ψ_λ, Ψ_μ) ≃ₜ M(TΨ_λ, TΨ_μ)`. -/
abbrev tmTrVec (i j : ι) (a : (S.tangentConstruction hU hcont).Tr (Φ i) (Φ j)) :
    (S.transPolyfold (S.tangentFamilyData hU hcont Φ i)
      (S.tangentFamilyData hU hcont Φ j)).TangentSpace :=
  (tangentTrHomeomorph (S := S) hU _ _).symm (S.tmTrCast hU hcont Φ i j a)

/-- The functor on objects: `(λ, h) ↦ T(Sigma.mk λ)(h)`. -/
def tmFunObj (x : (S.tangentConstruction hU hcont).ModelObj (S.tangentFamilyLift hU hcont Φ)) :
    (S.modelEpGroupoid (S.tangentFamilyData hU hcont Φ)).PObj.TangentSpace :=
  modelTObjMk (S.tangentFamilyData hU hcont Φ) x.1.down (S.tmObjCast hU hcont Φ x.1.down x.2)

/-- The functor on morphisms: `((λ, μ), a) ↦ T(Sigma.mk (λ, μ))(v)`, `v ∈ TM(Ψ_λ, Ψ_μ)` the vector
of `a`. -/
def tmFunMor (φ : (S.tangentConstruction hU hcont).ModelMor (S.tangentFamilyLift hU hcont Φ)) :
    (S.modelEpGroupoid (S.tangentFamilyData hU hcont Φ)).PMor.TangentSpace :=
  modelTMorMk (S.tangentFamilyData hU hcont Φ) (φ.1.1.down, φ.1.2.down)
    (S.tmTrVec hU hcont Φ φ.1.1.down φ.1.2.down φ.2)

theorem isLocalScDiffeo_tmObjCast (i : ι) :
    (Φ i).1.P.IsLocalScDiffeo (S.tangentFamilyData hU hcont Φ i).1.P.tangentPolyfold
      (S.tmObjCast hU hcont Φ i) :=
  (S.tangentObjCast_spec hU hcont _ _ (S.tangentData_eq hU hcont (Φ i))).2.1

theorem isLocalScDiffeo_tmTrCast (i j : ι) :
    ((S.tangentConstruction hU hcont).transPolyfold (Φ i) (Φ j)).IsLocalScDiffeo
      (S.tangentTrPolyfold hU _ _) (S.tmTrCast hU hcont Φ i j) :=
  (S.tangentTrCast_spec hU hcont _ _ _ _ (S.tangentData_eq hU hcont (Φ i))
    (S.tangentData_eq hU hcont (Φ j))).2.1

theorem tmTrCast_spec (i j : ι) (a : (S.tangentConstruction hU hcont).Tr (Φ i) (Φ j)) :
    (S.tmTrCast hU hcont Φ i j a).src = S.tmObjCast hU hcont Φ i a.src ∧
      (S.tmTrCast hU hcont Φ i j a).tgt = S.tmObjCast hU hcont Φ j a.tgt ∧
      (S.tmTrCast hU hcont Φ i j a).mor = (show S.TangentCatMor from a.mor) :=
  (S.tangentTrCast_spec hU hcont _ _ _ _ _ _).2.2 a

theorem tangentTrMap_tmTrVec (i j : ι) (a : (S.tangentConstruction hU hcont).Tr (Φ i) (Φ j)) :
    tangentTrMap hU (S.tmTrVec hU hcont Φ i j a) = S.tmTrCast hU hcont Φ i j a :=
  (tangentTrHomeomorph (S := S) hU _ _).apply_symm_apply _

theorem trTSrc_tmTrVec (i j : ι) (a : (S.tangentConstruction hU hcont).Tr (Φ i) (Φ j)) :
    S.trTSrc _ _ (S.tmTrVec hU hcont Φ i j a) = S.tmObjCast hU hcont Φ i a.src := by
  rw [← tangentTrMap_src (hU := hU), tangentTrMap_tmTrVec]
  exact (S.tmTrCast_spec hU hcont Φ i j a).1

theorem trTTgt_tmTrVec (i j : ι) (a : (S.tangentConstruction hU hcont).Tr (Φ i) (Φ j)) :
    S.trTTgt _ _ (S.tmTrVec hU hcont Φ i j a) = S.tmObjCast hU hcont Φ j a.tgt := by
  rw [← tangentTrMap_tgt (hU := hU), tangentTrMap_tmTrVec]
  exact (S.tmTrCast_spec hU hcont Φ i j a).2.1

theorem tmFunMor_src
    (φ : (S.tangentConstruction hU hcont).ModelMor (S.tangentFamilyLift hU hcont Φ)) :
    (S.modelEpGroupoid (S.tangentFamilyData hU hcont Φ)).tSrc (S.tmFunMor hU hcont Φ φ) =
      S.tmFunObj hU hcont Φ (((S.tangentConstruction hU hcont).modelGroupoid _).src φ) := by
  rw [tmFunMor, tSrc_modelTMorMk, trTSrc_tmTrVec]
  rfl

theorem tmFunMor_tgt
    (φ : (S.tangentConstruction hU hcont).ModelMor (S.tangentFamilyLift hU hcont Φ)) :
    (S.modelEpGroupoid (S.tangentFamilyData hU hcont Φ)).tTgt (S.tmFunMor hU hcont Φ φ) =
      S.tmFunObj hU hcont Φ (((S.tangentConstruction hU hcont).modelGroupoid _).tgt φ) := by
  rw [tmFunMor, tTgt_modelTMorMk, trTTgt_tmTrVec]
  rfl

/-- `TΓ_Ψ ∘ F = Γ^{TF}_Φ` on objects. -/
theorem tangentModelObj_tmFunObj
    (x : (S.tangentConstruction hU hcont).ModelObj (S.tangentFamilyLift hU hcont Φ)) :
    S.tangentModelObj hU (S.tangentFamilyData hU hcont Φ) (S.tmFunObj hU hcont Φ x) =
      ((S.tangentConstruction hU hcont).modelFunctor (S.tangentFamilyLift hU hcont Φ)).obj x := by
  rw [tmFunObj, tangentModelObj_mk]
  exact ((S.tangentObjCast_spec hU hcont _ _ (S.tangentData_eq hU hcont (Φ x.1.down))).2.2 x.2).symm

/-- `TΓ_Ψ ∘ F = Γ^{TF}_Φ` on morphisms. -/
theorem tangentModelMor_tmFunMor
    (φ : (S.tangentConstruction hU hcont).ModelMor (S.tangentFamilyLift hU hcont Φ)) :
    S.tangentModelMor hU (S.tangentFamilyData hU hcont Φ) (S.tmFunMor hU hcont Φ φ) =
      ((S.tangentConstruction hU hcont).modelFunctor (S.tangentFamilyLift hU hcont Φ)).mor φ := by
  rw [tmFunMor, tangentModelMor_mk, tangentTrMap_tmTrVec]
  exact (S.tmTrCast_spec hU hcont Φ _ _ φ.2).2.2

/-- `TΓ_Ψ` reflects equality of morphisms of `T(X_Ψ)` with the same source and target. -/
theorem tm_eq_of_tangentModelMor {ι : Type u} {Ψ : ι → S.Unif}
    {v w : (S.modelEpGroupoid Ψ).PMor.TangentSpace}
    (hs : (S.modelEpGroupoid Ψ).tSrc v = (S.modelEpGroupoid Ψ).tSrc w)
    (ht : (S.modelEpGroupoid Ψ).tTgt v = (S.modelEpGroupoid Ψ).tTgt w)
    (hm : S.tangentModelMor hU Ψ v = S.tangentModelMor hU Ψ w) : v = w :=
  (GroupoidFunctor.faithful_iff _).1 (S.tangentModelFunctor_faithful hU Ψ) v w hs ht hm

/-- **The functor `F : X^{TF}_Φ → T(X_Ψ)`**, `Ψ = tangentData ∘ Φ` (pp. 782–783): `(λ, h) ↦
T(Sigma.mk λ)(h)` on objects, `((λ, μ), a) ↦ T(Sigma.mk (λ, μ))(v)` on morphisms, `v ∈ TM(Ψ_λ, Ψ_μ)`
the vector of `a ∈ M(TΨ_λ, TΨ_μ)`. -/
def tangentModelIsoFunctor :
    EpFunctor ((S.tangentConstruction hU hcont).modelEpGroupoid (S.tangentFamilyLift hU hcont Φ))
      (S.modelEpGroupoid (S.tangentFamilyData hU hcont Φ)).tangentEpGroupoid where
  obj := S.tmFunObj hU hcont Φ
  mor := S.tmFunMor hU hcont Φ
  src_mor φ := S.tmFunMor_src hU hcont Φ φ
  tgt_mor φ := S.tmFunMor_tgt hU hcont Φ φ
  mor_comp φ ψ h := by
    let X := S.modelEpGroupoid (S.tangentFamilyData hU hcont Φ)
    let Y := (S.tangentConstruction hU hcont).modelGroupoid (S.tangentFamilyLift hU hcont Φ)
    have h' : X.tSrc (S.tmFunMor hU hcont Φ φ) = X.tTgt (S.tmFunMor hU hcont Φ ψ) := by
      rw [S.tmFunMor_src, S.tmFunMor_tgt]
      exact congrArg _ h
    refine S.tm_eq_of_tangentModelMor hU ?_ ?_ ?_
    · change _ = X.tSrc (X.tComp _ _)
      rw [(X.lemma_8_1_3 h').1, S.tmFunMor_src, S.tmFunMor_src]
      exact congrArg _ (Y.src_comp φ ψ h)
    · change _ = X.tTgt (X.tComp _ _)
      rw [(X.lemma_8_1_3 h').2, S.tmFunMor_tgt, S.tmFunMor_tgt]
      exact congrArg _ (Y.tgt_comp φ ψ h)
    · have hc := (S.tangentModelFunctor hU (S.tangentFamilyData hU hcont Φ)).mor_comp _ _ h'
      rw [tangentModelFunctor_mor, tangentModelFunctor_mor, tangentModelFunctor_mor,
        S.tangentModelMor_tmFunMor, S.tangentModelMor_tmFunMor] at hc
      rw [S.tangentModelMor_tmFunMor]
      exact (((S.tangentConstruction hU hcont).modelFunctor _).mor_comp φ ψ h).trans hc.symm
  mor_unit x := by
    let X := S.modelEpGroupoid (S.tangentFamilyData hU hcont Φ)
    let Y := (S.tangentConstruction hU hcont).modelGroupoid (S.tangentFamilyLift hU hcont Φ)
    refine S.tm_eq_of_tangentModelMor hU ?_ ?_ ?_
    · change _ = X.tSrc (X.tUnit _)
      rw [X.tSrc_tUnit, S.tmFunMor_src]
      exact congrArg _ (Y.src_unit x)
    · change _ = X.tTgt (X.tUnit _)
      rw [X.tTgt_tUnit, S.tmFunMor_tgt]
      exact congrArg _ (Y.tgt_unit x)
    · have hc := (S.tangentModelFunctor hU (S.tangentFamilyData hU hcont Φ)).mor_unit
        (S.tmFunObj hU hcont Φ x)
      rw [tangentModelFunctor_mor, tangentModelFunctor_obj, S.tangentModelObj_tmFunObj] at hc
      rw [S.tangentModelMor_tmFunMor]
      exact (((S.tangentConstruction hU hcont).modelFunctor _).mor_unit x).trans hc.symm
  isScSmoothMap_obj := by
    refine (MPolyfold.isScSmoothMap_sigma_iff _).2 fun i => ?_
    exact ((MPolyfold.isLocalScDiffeo_sigmaMk (fun k => (S.tangentFamilyData hU hcont Φ k).1.P)
      i.down).tangentMap.comp (S.isLocalScDiffeo_tmObjCast hU hcont Φ i.down)).isScSmoothMap
  isScSmoothMap_mor := by
    refine (MPolyfold.isScSmoothMap_sigma_iff _).2 fun p => ?_
    exact (((MPolyfold.isLocalScDiffeo_sigmaMk (fun q : ι × ι => S.transPolyfold
      (S.tangentFamilyData hU hcont Φ q.1) (S.tangentFamilyData hU hcont Φ q.2))
        (p.1.down, p.2.down)).tangentMap.comp isLocalScDiffeo_tangentTrHomeomorph_symm).comp
      (S.isLocalScDiffeo_tmTrCast hU hcont Φ p.1.down p.2.down)).isScSmoothMap

@[simp] theorem tangentModelIsoFunctor_obj
    (x : (S.tangentConstruction hU hcont).ModelObj (S.tangentFamilyLift hU hcont Φ)) :
    (S.tangentModelIsoFunctor hU hcont Φ).obj x = S.tmFunObj hU hcont Φ x := rfl

@[simp] theorem tangentModelIsoFunctor_mor
    (φ : (S.tangentConstruction hU hcont).ModelMor (S.tangentFamilyLift hU hcont Φ)) :
    (S.tangentModelIsoFunctor hU hcont Φ).mor φ = S.tmFunMor hU hcont Φ φ := rfl

theorem bijective_tmObjCast (i : ι) : Bijective (S.tmObjCast hU hcont Φ i) :=
  (S.tangentObjCast_spec hU hcont _ _ (S.tangentData_eq hU hcont (Φ i))).1

theorem bijective_tmTrVec (i j : ι) : Bijective (S.tmTrVec hU hcont Φ i j) :=
  (tangentTrHomeomorph (S := S) hU _ _).symm.bijective.comp
    (S.tangentTrCast_spec hU hcont _ _ _ _ (S.tangentData_eq hU hcont (Φ i))
      (S.tangentData_eq hU hcont (Φ j))).1

/-- **`F` is bijective on objects**: `Σ_λ O_{Φ_λ} = Σ_λ TO_λ = T(Σ_λ O_λ)`. -/
theorem bijective_tangentModelIsoFunctor_obj :
    Bijective (S.tangentModelIsoFunctor hU hcont Φ).obj := by
  constructor
  · rintro ⟨i, x⟩ ⟨j, y⟩ h
    rw [tangentModelIsoFunctor_obj, tangentModelIsoFunctor_obj, tmFunObj, tmFunObj] at h
    obtain ⟨hij, hxy⟩ := MPolyfold.sigmaTangent_mk_inj
      (fun k => (S.tangentFamilyData hU hcont Φ k).1.P) h
    obtain rfl : i = j := ULift.ext _ _ hij
    obtain rfl := (S.bijective_tmObjCast hU hcont Φ i.down).1 (eq_of_heq hxy)
    rfl
  · intro v
    obtain ⟨i, k, rfl⟩ := exists_modelTObjMk v
    obtain ⟨x, rfl⟩ := (S.bijective_tmObjCast hU hcont Φ i).2 k
    exact ⟨⟨ULift.up i, x⟩, rfl⟩

/-- **`F` is bijective on morphisms**: `Σ M(Φ_λ, Φ_μ) = Σ M(TΨ_λ, TΨ_μ) = Σ TM(Ψ_λ, Ψ_μ) =
T(Σ M(Ψ_λ, Ψ_μ))`. -/
theorem bijective_tangentModelIsoFunctor_mor :
    Bijective (S.tangentModelIsoFunctor hU hcont Φ).mor := by
  constructor
  · rintro ⟨⟨i, j⟩, a⟩ ⟨⟨i', j'⟩, a'⟩ h
    rw [tangentModelIsoFunctor_mor, tangentModelIsoFunctor_mor, tmFunMor, tmFunMor] at h
    obtain ⟨hp, ha⟩ := MPolyfold.sigmaTangent_mk_inj
      (fun q : ι × ι => S.transPolyfold (S.tangentFamilyData hU hcont Φ q.1)
        (S.tangentFamilyData hU hcont Φ q.2)) h
    obtain ⟨hi, hj⟩ := Prod.mk.inj hp
    obtain rfl : i = i' := ULift.ext _ _ hi
    obtain rfl : j = j' := ULift.ext _ _ hj
    obtain rfl := (S.bijective_tmTrVec hU hcont Φ i.down j.down).1 (eq_of_heq ha)
    rfl
  · intro W
    obtain ⟨⟨i, j⟩, w, rfl⟩ := exists_modelTMorMk W
    obtain ⟨a, rfl⟩ := (S.bijective_tmTrVec hU hcont Φ i j).2 w
    exact ⟨⟨(ULift.up i, ULift.up j), a⟩, rfl⟩

/-- `F` is a local sc-diffeomorphism on objects. -/
theorem isLocalScDiffeo_tangentModelIsoFunctor_obj :
    ((S.tangentConstruction hU hcont).modelEpGroupoid
        (S.tangentFamilyLift hU hcont Φ)).PObj.IsLocalScDiffeo
      (S.modelEpGroupoid (S.tangentFamilyData hU hcont Φ)).tangentEpGroupoid.PObj
      (S.tangentModelIsoFunctor hU hcont Φ).obj :=
  (MPolyfold.isLocalScDiffeo_sigma_iff _).2 fun i =>
    (MPolyfold.isLocalScDiffeo_sigmaMk (fun k => (S.tangentFamilyData hU hcont Φ k).1.P)
      i.down).tangentMap.comp (S.isLocalScDiffeo_tmObjCast hU hcont Φ i.down)

/-- `F` is a local sc-diffeomorphism on morphisms. -/
theorem isLocalScDiffeo_tangentModelIsoFunctor_mor :
    ((S.tangentConstruction hU hcont).modelEpGroupoid
        (S.tangentFamilyLift hU hcont Φ)).PMor.IsLocalScDiffeo
      (S.modelEpGroupoid (S.tangentFamilyData hU hcont Φ)).tangentEpGroupoid.PMor
      (S.tangentModelIsoFunctor hU hcont Φ).mor :=
  (MPolyfold.isLocalScDiffeo_sigma_iff _).2 fun p =>
    ((MPolyfold.isLocalScDiffeo_sigmaMk (fun q : ι × ι => S.transPolyfold
      (S.tangentFamilyData hU hcont Φ q.1) (S.tangentFamilyData hU hcont Φ q.2))
        (p.1.down, p.2.down)).tangentMap.comp isLocalScDiffeo_tangentTrHomeomorph_symm).comp
      (S.isLocalScDiffeo_tmTrCast hU hcont Φ p.1.down p.2.down)

theorem tangentModelIsoFunctor_full : (S.tangentModelIsoFunctor hU hcont Φ).toFunctor.Full :=
  ((S.tangentModelIsoFunctor hU hcont Φ).toGroupoidFunctor.full_faithful_essSurj_of_bijective
    (S.bijective_tangentModelIsoFunctor_obj hU hcont Φ)
    (S.bijective_tangentModelIsoFunctor_mor hU hcont Φ)).1

theorem tangentModelIsoFunctor_faithful :
    (S.tangentModelIsoFunctor hU hcont Φ).toFunctor.Faithful :=
  ((S.tangentModelIsoFunctor hU hcont Φ).toGroupoidFunctor.full_faithful_essSurj_of_bijective
    (S.bijective_tangentModelIsoFunctor_obj hU hcont Φ)
    (S.bijective_tangentModelIsoFunctor_mor hU hcont Φ)).2.1

theorem tangentModelIsoFunctor_essSurj :
    (S.tangentModelIsoFunctor hU hcont Φ).toFunctor.EssSurj :=
  ((S.tangentModelIsoFunctor hU hcont Φ).toGroupoidFunctor.full_faithful_essSurj_of_bijective
    (S.bijective_tangentModelIsoFunctor_obj hU hcont Φ)
    (S.bijective_tangentModelIsoFunctor_mor hU hcont Φ)).2.2

/-- **`F : X^{TF}_Φ → T(X_Ψ)` is an equivalence of ep-groupoids** (Definition 10.1.1, through
Lemma 10.1.2): full, faithful, essentially surjective and a local sc-diffeomorphism on objects. -/
theorem isEquivalence_tangentModelIsoFunctor :
    (S.tangentModelIsoFunctor hU hcont Φ).IsEquivalence :=
  EpFunctor.lemma_10_1_2 _
    { faithful := S.tangentModelIsoFunctor_faithful hU hcont Φ
      full := S.tangentModelIsoFunctor_full hU hcont Φ
      essSurj := S.tangentModelIsoFunctor_essSurj hU hcont Φ }
    (S.isLocalScDiffeo_tangentModelIsoFunctor_obj hU hcont Φ)

/-- **`TΓ_Ψ ∘ F = Γ^{TF}_Φ` on objects.** -/
theorem tangentModelFunctor_comp_tangentModelIsoFunctor_obj
    (x : (S.tangentConstruction hU hcont).ModelObj (S.tangentFamilyLift hU hcont Φ)) :
    (S.tangentModelFunctor hU (S.tangentFamilyData hU hcont Φ)).obj
        ((S.tangentModelIsoFunctor hU hcont Φ).obj x) =
      ((S.tangentConstruction hU hcont).modelFunctor (S.tangentFamilyLift hU hcont Φ)).obj x :=
  S.tangentModelObj_tmFunObj hU hcont Φ x

/-- **`TΓ_Ψ ∘ F = Γ^{TF}_Φ` on morphisms.** -/
theorem tangentModelFunctor_comp_tangentModelIsoFunctor_mor
    (φ : (S.tangentConstruction hU hcont).ModelMor (S.tangentFamilyLift hU hcont Φ)) :
    (S.tangentModelFunctor hU (S.tangentFamilyData hU hcont Φ)).mor
        ((S.tangentModelIsoFunctor hU hcont Φ).mor φ) =
      ((S.tangentConstruction hU hcont).modelFunctor (S.tangentFamilyLift hU hcont Φ)).mor φ :=
  S.tangentModelMor_tmFunMor hU hcont Φ φ

/-- `|TΓ_Ψ| ∘ |F| = |Γ^{TF}_Φ|`. -/
theorem orbitMap_tangentModelFunctor_comp_tangentModelIsoFunctor :
    (S.tangentModelFunctor hU (S.tangentFamilyData hU hcont Φ)).orbitMap ∘
        (S.tangentModelIsoFunctor hU hcont Φ).orbitMap =
      ((S.tangentConstruction hU hcont).modelFunctor
        (S.tangentFamilyLift hU hcont Φ)).orbitMap := by
  funext z
  induction z using Quotient.inductionOn with
  | h x =>
    exact congrArg S.tangentCatGroupoid.π
      (S.tangentModelFunctor_comp_tangentModelIsoFunctor_obj hU hcont Φ x)

/-- **The model `X^{TF}_Φ` of `(TF, M)` and the tangent `T(X_Ψ)` of the model of `C`**
(pp. 782–783), for every family `Φ` of `TF` and `Ψ = tangentData ∘ Φ` (`Φ_λ = TΨ_λ`):
`F : X^{TF}_Φ → T(X_Ψ)` is an equivalence of ep-groupoids (Definition 10.1.1), indeed an
isomorphism (bijective and a local sc-diffeomorphism on objects and on morphisms), `|F|` is a
homeomorphism, and `TΓ_Ψ ∘ F = Γ^{TF}_Φ` on objects and morphisms. -/
theorem tangentModelIso_spec :
    (S.tangentModelIsoFunctor hU hcont Φ).IsEquivalence ∧
      Bijective (S.tangentModelIsoFunctor hU hcont Φ).obj ∧
      Bijective (S.tangentModelIsoFunctor hU hcont Φ).mor ∧
      ((S.tangentConstruction hU hcont).modelEpGroupoid
          (S.tangentFamilyLift hU hcont Φ)).PObj.IsLocalScDiffeo
        (S.modelEpGroupoid (S.tangentFamilyData hU hcont Φ)).tangentEpGroupoid.PObj
        (S.tangentModelIsoFunctor hU hcont Φ).obj ∧
      ((S.tangentConstruction hU hcont).modelEpGroupoid
          (S.tangentFamilyLift hU hcont Φ)).PMor.IsLocalScDiffeo
        (S.modelEpGroupoid (S.tangentFamilyData hU hcont Φ)).tangentEpGroupoid.PMor
        (S.tangentModelIsoFunctor hU hcont Φ).mor ∧
      IsHomeomorph (S.tangentModelIsoFunctor hU hcont Φ).orbitMap ∧
      (∀ x, (S.tangentModelFunctor hU (S.tangentFamilyData hU hcont Φ)).obj
          ((S.tangentModelIsoFunctor hU hcont Φ).obj x) =
        ((S.tangentConstruction hU hcont).modelFunctor (S.tangentFamilyLift hU hcont Φ)).obj x) ∧
      ∀ φ, (S.tangentModelFunctor hU (S.tangentFamilyData hU hcont Φ)).mor
          ((S.tangentModelIsoFunctor hU hcont Φ).mor φ) =
        ((S.tangentConstruction hU hcont).modelFunctor (S.tangentFamilyLift hU hcont Φ)).mor φ :=
  ⟨S.isEquivalence_tangentModelIsoFunctor hU hcont Φ,
    S.bijective_tangentModelIsoFunctor_obj hU hcont Φ,
    S.bijective_tangentModelIsoFunctor_mor hU hcont Φ,
    S.isLocalScDiffeo_tangentModelIsoFunctor_obj hU hcont Φ,
    S.isLocalScDiffeo_tangentModelIsoFunctor_mor hU hcont Φ,
    (S.isEquivalence_tangentModelIsoFunctor hU hcont Φ).isHomeomorph_orbitMap,
    S.tangentModelFunctor_comp_tangentModelIsoFunctor_obj hU hcont Φ,
    S.tangentModelFunctor_comp_tangentModelIsoFunctor_mor hU hcont Φ⟩

end ModelIso

/-! ### A covering family of `TF` indexed in the universe of `C` -/

section Cover

variable (hU : S.HasUniformizers) (hcont : ∀ Ψ : S.Unif, Continuous (S.hat Ψ))

/-- The object `[α, Ψ_α, 0]` of `TC` over an object `α` of `C¹` with `F(α) ≠ ∅`. -/
def tangentZeroObj (α : {α : C.Obj // S.TangentObj α}) : S.TangentCatObj :=
  ⟨α.1, α.2, 0⟩

/-- **The tangent uniformizer `TΨ_α ∈ TF([α, Ψ_α, 0])`** of the reference uniformizer `Ψ_α` of
an object `α` of `C¹` with `F(α) ≠ ∅`. -/
def tangentRefFamily (α : {α : C.Obj // S.TangentObj α}) :
    (S.tangentConstruction hU hcont).Unif :=
  ⟨S.tangentUnif hU (S.refUnif α.2) (hcont _), S.tangentZeroObj α,
    S.refUnif α.2, refUnif_mem α.2, rfl⟩

/-- **The covering family `(TΨ_α)_α` of `TF`**, `α` running over the objects of `C¹` with
`F(α) ≠ ∅` (an index type in the universe of `C`, lifted to that of `TC`). -/
def tangentRefCover : (S.tangentConstruction hU hcont).CoveringFamily where
  ι := ULift.{1} {α : C.Obj // S.TangentObj α}
  Ψ := S.tangentFamilyLift hU hcont (S.tangentRefFamily hU hcont)
  cover := eq_univ_of_forall fun z => by
    induction z using Quotient.inductionOn with
    | h β =>
      refine mem_iUnion.2 ⟨ULift.up ⟨(show S.TangentCatObj from β).base,
        (show S.TangentCatObj from β).isObj⟩, ?_⟩
      obtain ⟨k, hk⟩ := tangentUnif_isAt hU hcont (β := β)
        (refUnif_mem (show S.TangentCatObj from β).isObj)
      exact (S.tangentUnif hU _ (hcont _)).mem_footprint_iff.2 ⟨k, congrArg _ hk⟩

/-- **The model of `(TF, M)` on the covering family `(TΨ_α)_α` and the tangent of the model of
`C` on `Ψ = tangentData ∘ (TΨ_α)_α`**: `F : X^{TF} → T(X_Ψ)` is an equivalence of ep-groupoids,
`X^{TF} → TC` is an equivalence (Lemma 17.1.15 for `(TF, M)`) with `|·|` a homeomorphism, and
`TΓ_Ψ ∘ F = Γ^{TF}` (so `TΓ_Ψ : T(X_Ψ) → TC` is full, faithful and essentially surjective, while
`Ψ` need not be a covering family of `C`). -/
theorem tangentModel_equivalence :
    (S.tangentModelIsoFunctor hU hcont (S.tangentRefFamily hU hcont)).IsEquivalence ∧
      ((S.tangentConstruction hU hcont).modelFunctor
        (S.tangentRefCover hU hcont).Ψ).toFunctor.IsEquivalence ∧
      IsHomeomorph ((S.tangentConstruction hU hcont).modelFunctor
        (S.tangentRefCover hU hcont).Ψ).orbitMap ∧
      (S.tangentModelFunctor hU (S.tangentFamilyData hU hcont
          (S.tangentRefFamily hU hcont))).orbitMap ∘
          (S.tangentModelIsoFunctor hU hcont (S.tangentRefFamily hU hcont)).orbitMap =
        ((S.tangentConstruction hU hcont).modelFunctor (S.tangentRefCover hU hcont).Ψ).orbitMap ∧
      (S.tangentModelFunctor hU (S.tangentFamilyData hU hcont
        (S.tangentRefFamily hU hcont))).toFunctor.IsEquivalence := by
  have hF := S.isEquivalence_tangentModelIsoFunctor hU hcont (S.tangentRefFamily hU hcont)
  obtain ⟨hΓ, hΓo⟩ := (S.tangentConstruction hU hcont).lemma_17_1_15 (S.tangentRefCover hU hcont)
  refine ⟨hF, hΓ, hΓo, S.orbitMap_tangentModelFunctor_comp_tangentModelIsoFunctor hU hcont _, ?_⟩
  have hE : (S.tangentModelFunctor hU (S.tangentFamilyData hU hcont
      (S.tangentRefFamily hU hcont))).toFunctor.EssSurj := by
    refine (GroupoidFunctor.essSurj_iff _).2 fun e => ?_
    obtain ⟨x, ψ, hs, ht⟩ := (GroupoidFunctor.essSurj_iff _).1 hΓ.essSurj e
    exact ⟨(S.tangentModelIsoFunctor hU hcont _).obj x, ψ,
      hs.trans (S.tangentModelFunctor_comp_tangentModelIsoFunctor_obj hU hcont _ x).symm, ht⟩
  exact { full := S.tangentModelFunctor_full hU _
          faithful := S.tangentModelFunctor_faithful hU _
          essSurj := hE }

end Cover

/-! ### The witness: the reflection `ℤ/2 ⋉ ℝ` -/

section Reflection

open EpGroupoid.Examples MPolyfold

/-- The zero vector of `T_0ℝ`, in the chart `y ↦ y`. -/
def reflZeroVec : (rnChart 1 0).model.E.tangent 0 := ((0 : Fin 1 → ℝ), (0 : Fin 1 → ℝ))

theorem reflZeroVec_mem : reflZeroVec ∈ retractTangent (rnChart 1 0).model.E
    (rnChart 1 0).model.C (rnChart 1 0).model.O := by
  change reflZeroVec ∈ retractTangent (rnSc 1) univ univ
  rw [retractTangent_univ]
  exact mem_univ _

/-- `[0, y ↦ y, 0] ∈ T_0ℝ`. -/
def reflZeroTangent : (rnPolyfold 1).TangentSpace :=
  TangentSpace.mk (TangentPre.ofVec (isChart_rnChart 0) reflZeroVec_mem)

theorem tangentChartMap_reflZeroTangent :
    tangentChartMap (isChart_rnChart 0) reflZeroTangent = reflZeroVec :=
  tangentChartMap_mk_ofVec _ reflZeroVec_mem

/-- **`T(y ↦ −y)` fixes the zero vector of `T_0ℝ`.** -/
theorem tangentMap_neg_reflZeroTangent :
    MPolyfold.tangentMap (isScSmoothMap_units_smul (-1)) reflZeroTangent = reflZeroTangent := by
  refine tangentChartMap_injOn (isChart_rnChart 0) (mem_univ _) (mem_univ _) ?_
  rw [tangentChartMap_tangentMap_of_linear (isScSmoothMap_units_smul (-1)) (isChart_rnChart 0)
    (isChart_rnChart 0) (ScOperator.ofConst (-ContinuousLinearMap.id ℝ (Fin 1 → ℝ)))
    (fun _ _ => mem_univ _) (fun x _ => ?_) (mem_univ _), tangentChartMap_reflZeroTangent]
  · refine Prod.ext ?_ ?_
    · change -(0 : Fin 1 → ℝ) = 0
      exact neg_zero
    · change -(0 : Fin 1 → ℝ) = 0
      exact neg_zero
  · change (-1 : ℤˣ) • x - 0 = -(x - 0)
    rw [units_smul_rn_neg_one, sub_zero, sub_zero]

/-- The object `TΨ₀(0)` of `TC` (the zero vector over `0`). -/
abbrev reflTangentObj : reflectionConstruction.TangentCatObj :=
  reflectionConstruction.tangentUnifObj reflectionConstruction_hasUniformizers reflectionUnif
    reflZeroTangent

/-- **`TΨ₀ ∈ TF`**, the tangent uniformizer of the reflection uniformizer `Ψ₀`. -/
def reflTangentUnif : reflectionTangentConstruction.Unif :=
  ⟨reflectionConstruction.tangentUnif reflectionConstruction_hasUniformizers reflectionUnif
      (reflection_continuous_hat_all _), reflTangentObj, reflectionUnif, rfl, rfl⟩

/-- The one-element family `(TΨ₀)` of `TF`. -/
abbrev reflTangentFamily : Unit → reflectionTangentConstruction.Unif := fun _ => reflTangentUnif

/-- **`(TΨ₀)` is a covering family of `TF`**: every object of `TC` is `TΨ₀(k)`. -/
def reflectionTangentCover : reflectionTangentConstruction.CoveringFamily where
  ι := ULift.{1} Unit
  Ψ := reflectionConstruction.tangentFamilyLift reflectionConstruction_hasUniformizers
    reflection_continuous_hat_all reflTangentFamily
  cover := eq_univ_of_forall fun z => by
    induction z using Quotient.inductionOn with
    | h β =>
      refine mem_iUnion.2 ⟨ULift.up (), ?_⟩
      obtain ⟨k, -, hk⟩ := exists_tangentUnifObj_eq reflectionConstruction_hasUniformizers
        reflectionUnif (show reflectionConstruction.TangentCatObj from β)
        (show reflectionConstruction.TangentCatObj from β).base rfl
      exact (reflectionConstruction.tangentUnif reflectionConstruction_hasUniformizers
        reflectionUnif (reflection_continuous_hat_all _)).mem_footprint_iff.2 ⟨k, congrArg _ hk⟩

/-- The automorphism `TΨ₀(−1, 0)` of `TΨ₀(0)` in `M(TΨ₀, TΨ₀)`. -/
def reflTangentAut : reflectionTangentConstruction.Tr reflTangentUnif reflTangentUnif :=
  ⟨reflZeroTangent, reflectionConstruction.tangentUnifMor reflectionConstruction_hasUniformizers
      reflectionUnif (ULift.up (-1 : ℤˣ), reflZeroTangent), reflZeroTangent, rfl,
    (tangentUnifMor_tgt_of_continuous _ _ (reflection_continuous_hat_all _) _).trans
      (congrArg _ tangentMap_neg_reflZeroTangent)⟩

/-- **The non-degenerate witness** (non-trivial isotropy): for the reflection construction
(`ℤ/2 ⋉ ℝ`, every `Ψ̂` continuous) and the covering family `(TΨ₀)` of `TF`, the functor
`F : X^{TF} → T(X_Ψ)`, `Ψ = tangentData ∘ (TΨ₀)`, is an equivalence of ep-groupoids, `X^{TF} → TC`
is an equivalence, and `X^{TF}` has an automorphism (`TΨ₀(−1, 0)` of the zero vector over `0`)
other than the unit, whose image under `F` is not the unit of `T(X_Ψ)` either. -/
theorem reflectionTangentFamily_isotropy :
    (reflectionConstruction.tangentModelIsoFunctor reflectionConstruction_hasUniformizers
      reflection_continuous_hat_all reflTangentFamily).IsEquivalence ∧
    (reflectionTangentConstruction.modelFunctor
      reflectionTangentCover.Ψ).toFunctor.IsEquivalence ∧
    ∃ m : reflectionTangentConstruction.ModelMor reflectionTangentCover.Ψ,
      (reflectionTangentConstruction.modelEP reflectionTangentCover.Ψ).X.src m =
          (reflectionTangentConstruction.modelEP reflectionTangentCover.Ψ).X.tgt m ∧
        m ≠ (reflectionTangentConstruction.modelEP reflectionTangentCover.Ψ).X.unit
          ((reflectionTangentConstruction.modelEP reflectionTangentCover.Ψ).X.src m) ∧
        (reflectionConstruction.tangentModelIsoFunctor reflectionConstruction_hasUniformizers
            reflection_continuous_hat_all reflTangentFamily).mor m ≠
          (reflectionConstruction.modelEpGroupoid (reflectionConstruction.tangentFamilyData
              reflectionConstruction_hasUniformizers reflection_continuous_hat_all
              reflTangentFamily)).tangentEpGroupoid.unit
            ((reflectionConstruction.tangentModelIsoFunctor reflectionConstruction_hasUniformizers
              reflection_continuous_hat_all reflTangentFamily).obj
              ((reflectionTangentConstruction.modelEP reflectionTangentCover.Ψ).X.src m)) := by
  set F := reflectionConstruction.tangentModelIsoFunctor reflectionConstruction_hasUniformizers
    reflection_continuous_hat_all reflTangentFamily
  let m : reflectionTangentConstruction.ModelMor reflectionTangentCover.Ψ :=
    ⟨(ULift.up (), ULift.up ()), reflTangentAut⟩
  have hne : m ≠ (reflectionTangentConstruction.modelEP reflectionTangentCover.Ψ).X.unit
      ((reflectionTangentConstruction.modelEP reflectionTangentCover.Ψ).X.src m) := fun h => by
    have h' := congrArg (fun m : reflectionTangentConstruction.ModelMor reflectionTangentCover.Ψ =>
      ((show reflectionConstruction.TangentCatMor from m.2.mor).mor : ℤˣ × (Fin 1 → ℝ)).1) h
    exact absurd h' (by decide)
  refine ⟨reflectionConstruction.isEquivalence_tangentModelIsoFunctor _ _ _,
    (reflectionTangentConstruction.lemma_17_1_15 reflectionTangentCover).1, m, rfl, hne,
    fun h => hne ?_⟩
  refine (reflectionConstruction.bijective_tangentModelIsoFunctor_mor _ _ _).1 (h.trans ?_)
  exact (F.mor_unit _).symm

end Reflection

end GCT.PolyfoldConstruction

end Polyfold
