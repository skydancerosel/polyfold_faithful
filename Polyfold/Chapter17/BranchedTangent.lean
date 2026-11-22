import Polyfold.Chapter17.BranchedSupport
import Polyfold.Chapter17.TangentModel
import Polyfold.Chapter9.GeneralCorollaries
import Polyfold.Chapter11.BranchedEquivalenceTangent

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.5 "Branched Ep⁺-Subcategories" (pp. 814–817): **Definition 17.5.6** (the tangent
`TΘ : TC → ℚ⁺`), **Proposition 17.5.7** (the section `TΘ` of `Gr(C) → C_∞`) and
**Definition 17.5.8** (orientations).  Numbers and pages are the 2021 text's.

# The tangent of a branched ep⁺-subcategory

## The text, paraphrased

(pp. 814–815) For a covering family `Ψ` with equivalence `Γ : X → C`, `Γ^*Θ` is a branched
ep⁺-subgroupoid with tangent `T(Γ^*Θ) : TX → ℚ⁺` (Definition 9.2.12); with `TΓ : TX → TC`
(17.52) one puts `(TΓ)_*(T(Γ^*Θ)) : TC → ℚ⁺`.  For a second covering family and the canonical
generalized isomorphism `f : X → X'`, `Tf_*(T(Γ^*Θ)) = T(Γ'^*Θ)`, so the push-forwards agree.
(Definition 17.5.6) `TΘ := (TΓ)_*(T(Γ^*Θ))` is the tangent of `Θ`.  (p. 815) `ν(α)` is the set of
finite formal sums `∑ σ_L · L`, `σ_L ∈ ℚ`, `σ_L ≥ 0`, of smooth finite-dimensional subspaces
`L ⊂ T_αC`, `ν(φ)(∑ σ_L · L) = ∑ σ_L · Tφ(L)`, and `Gr(C) → C_∞` is the associated category.
For `x ∈ X` smooth, `TΓ^*Θ(x)` is invariant under the isotropy `G_x` (17.86); for `φ : Γ(x) → α`
the image of `TΓ^*Θ(x)` under `TΓ` and then `Tφ` does not depend on `φ`.  (Proposition 17.5.7)
There is a well-defined section `TΘ` of `Gr(C) → C_∞` with `TΘ = TΓ_* T_{Θ∘Γ}` for every
covering family; "the straightforward proof is left to the reader".  (p. 817) `Gr̂(α)` consists
of the finite formal sums `∑ σ_L̂ · L̂` of smooth oriented finite-dimensional subspaces of `T_αC`,
`f : Gr̂(C) → Gr(C)` forgets the orientations (17.87), and for a covering family the pull-back
`(TΓ^*T̂)(x) = TΓ(x)⁻¹(T̂(Γ(x)))`.  (Definition 17.5.8) An orientation of `Θ` is a section functor
`T̂Θ` of `Gr̂(C) → C_∞` with `f ∘ T̂Θ = TΘ` whose pull-back `TΓ^*T̂Θ` is an orientation of `Γ^*Θ`
(Definition 9.3.2).  (Remark 17.5.9) The last condition can be replaced by: `TΨ^*T̂Θ` is an
orientation of `Θ ∘ Ψ` for `α ∈ supp(Θ)` and `Ψ ∈ F(α)`.

## What is formalized

* `modelTangentTheta Ψ Θ` (`T(Γ^*Θ) : T(X_Ψ) → ℚ⁺`, Chapter 9's `tangentTheta` of `Θ ∘ Γ_Ψ`),
  `tangentThetaVia hU Ψ Θ` (`(TΓ_Ψ)_*(T(Γ^*Θ))`, the push-forward of Chapter 17's
  `GroupoidFunctor.pushTheta` along `TΓ_Ψ = tangentModelFunctor`).
* On a summand: `modelTangentTheta_mk` (`T(Γ^*Θ)(Tι_λ k) = T(Θ ∘ Ψ_λ)(k)`, Chapter 11's
  `tangentTheta_tangentMapOn` for `ι_λ = Sigma.mk λ`), `tangentThetaVia_tangentUnifObj`.
* **Definition 17.5.6**: `tangentThetaVia_eq_of_comp` (a covering subfamily gives the same
  push-forward), `definition_17_5_6` (independence of the covering family), the tangent
  `branchedTangent hU Θ`, `branchedTangent_eq` (`= (TΓ)_*(T(Γ^*Θ))` for every covering family),
  `branchedTangent_tangentUnifObj` (`TΘ(TΨ(k)) = T(Θ ∘ Ψ)(k)` for every uniformizer `Ψ` of `F`),
  `branchedTangent_comp_tangentModelObj` (`(TΓ)^* TΘ = T(Γ^*Θ)`), `branchedTangent_nonneg`,
  `isFunctorial_branchedTangent`.
* **`Gr(C)`**: `tcMove φ` (`Tφ : T_αC → T_{α'}C`, the target of the morphism `(h̄, φ, Tφ(h̄))` of
  `TC`), `tcMove_tcMove`, `GrC α`, `grPushC` (`ν(φ)`), `grPushC_mem`, `grPushC_comp`.
* **Proposition 17.5.7**: `modelGrPush` (`Tφ ∘ TΓ` on formal sums), `tangentValue_model_mk`,
  `tangentModelObj_tangentMor` (`TΓ(Tψ(a)) = T(Γψ)(TΓ(a))`), `modelGrPush_tangentValue_eq`
  (the independence of `(x, φ)`, i.e. (17.86)), `tangentSectionVia`, `tangentSectionVia_eq`,
  `tangentSectionVia_eq_of_comp`, the section `branchedTangentSection hU Θ`, and
  `proposition_17_5_7`: values in `Gr(α)` for `α ∈ C¹`, the identity `TΘ = TΓ_* T_{Θ∘Γ}` for every
  covering family and every `φ : Γ(x) → α`, naturality `TΘ(α') = ν(χ)(TΘ(α))`, and uniqueness.
* **Definition 17.5.8**: `OrTC` (oriented subsets of `T_αC`), `GrHatC`, `grForgetC` (17.87),
  `OrTC.move`, `grHatPushC`, `orTCPull`, `sectionPull` (`TΓ^*T̂`), `IsOrientationC`; satisfiability
  `isOrientationC_zero` (with `branchedTangentSection_zero`).
* Remark 17.5.9 (the equivalence of the model condition with the condition on the uniformizers
  of `F` at points of `supp(Θ)`) is `remark_17_5_9_hyp` (`BranchedOrientation.lean`).

## Readings

* `T_αC` is the set of objects of `TC` over `α` (`TangentCatObj` with `base = α`), and `Gr(α)` is
  read, as in Chapter 9 (`EpGroupoid.Gr`, point G.7), as finite formal sums with non-negative
  rational weights of subsets of that fibre; the subspaces of the text are the images
  `Tφ(TΓ(T_xMᵢ))` of the tangent spaces `T_xMᵢ` of local branching structures.
* `C_∞` is read through `S.TangentObj α` (`α ∈ C¹` with `F(α) ≠ ∅`), which contains the smooth
  objects under `HasUniformizers`; the formulas are stated there.
* The text's comparison through the tangent of the canonical generalized isomorphism `f : X → X'`
  is replaced by the union of the two covering families: both models embed into the model of the
  union as summands, and on a summand `T(Γ^*Θ)` is Chapter 9's `TΘ` of `Θ ∘ Ψ_λ`.
* `TΘ` and the section `TΘ` are defined through the covering family `tangentCover hU` that
  defines the topology of `|TC|` (Proposition 17.2.16); `branchedTangent_eq` and
  `proposition_17_5_7` give the same objects for every covering family.
* An oriented subspace of `T_αC` is read, as Chapter 9's `MPolyfold.OrTangent`, as a set with a
  dimension and a set of positive frames; that the pull-backs are oriented finite-dimensional
  subspaces is part of the condition that `TΓ^*T̂Θ` is an orientation (`EpGroupoid.GrHat`).
  "For a covering set `Ψ`" in Definition 17.5.8 is read as "for every covering family".
* Chapter 9's `tangentTheta` and `tangentValue` are used with `hasIndependentTangentSums`
  (Theorem 9.2.1's independence, `GeneralCorollaries.lean`), with no further hypothesis.
-/

set_option maxSynthPendingDepth 3

open Set Function CategoryTheory

noncomputable section

namespace Polyfold

universe u

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} {S : C.PolyfoldConstruction}

/-! ### The model: `T(Γ^*Θ)` and its push-forward -/

section TangentTheta

variable (hU : S.HasUniformizers) {ι : Type u} (Ψ : ι → S.Unif)

variable (S) in
/-- **`T(Γ^*Θ) : T(X_Ψ) → ℚ⁺`** (2021 p. 815): Definition 9.2.12 for `Γ^*Θ = Θ ∘ Γ_Ψ`. -/
def modelTangentTheta (Θ : C.Obj → ℚ) : (S.modelEpGroupoid Ψ).PObj.TangentSpace → ℚ :=
  (S.modelEpGroupoid Ψ).tangentTheta (S.modelPull Ψ Θ)

/-- **`(TΓ_Ψ)_*(T(Γ^*Θ)) : TC → ℚ⁺`** (2021 p. 815, Definition 17.5.6). -/
def tangentThetaVia (Θ : C.Obj → ℚ) : S.TangentCatObj → ℚ :=
  (S.tangentModelFunctor hU Ψ).pushTheta (S.modelTangentTheta Ψ Θ)

variable {Ψ}

/-- `Γ^*Θ` is a branched ep⁺-subgroupoid of `X_Ψ` for every family. -/
theorem IsBranchedSubcategory.model {Θ : C.Obj → ℚ} (hΘ : S.IsBranchedSubcategory Θ) :
    (S.modelEpGroupoid Ψ).IsBranchedEpSubgroupoid (S.modelPull Ψ Θ) :=
  (isBranchedEpSubgroupoid_modelPull_iff hΘ.nonneg hΘ.isFunctorial).2 fun i => hΘ.unif (Ψ i)

theorem isFunctorial_modelTangentTheta {Θ : C.Obj → ℚ} (hΘ : S.IsBranchedSubcategory Θ) :
    (S.modelEpGroupoid Ψ).tangentGroupoidStr.IsFunctorial (S.modelTangentTheta Ψ Θ) :=
  (S.modelEpGroupoid Ψ).isFunctorial_tangentTheta hΘ.model
    ((S.modelEpGroupoid Ψ).hasIndependentTangentSums _)

/-- **`T(Γ^*Θ)` on a summand**: `T(Γ^*Θ)(Tι_λ(k)) = T(Θ ∘ Ψ_λ)(k)` for `ι_λ = Sigma.mk λ`. -/
theorem modelTangentTheta_mk {Θ : C.Obj → ℚ} (hΘ : S.IsBranchedSubcategory Θ) (i : ι)
    (k : (Ψ i).1.P.TangentSpace) :
    S.modelTangentTheta Ψ Θ (modelTObjMk Ψ i k) = (Ψ i).1.ep.tangentTheta (Θ ∘ (Ψ i).1.obj) k := by
  have hd := MPolyfold.isScDiffeoOn_sigmaMk (fun i => (Ψ i).1.P) i (basePt (Ψ i) k)
  have h := EpGroupoid.tangentTheta_tangentMapOn (X := (Ψ i).1.ep) (Y := S.modelEpGroupoid Ψ)
    (Θ' := S.modelPull Ψ Θ) hd (fun _ _ => rfl) (hΘ.unif (Ψ i))
    ((Ψ i).1.ep.hasIndependentTangentSums _) ((S.modelEpGroupoid Ψ).hasIndependentTangentSums _)
    (α := k) (mem_univ _)
  exact (congrArg _ (congrFun (MPolyfold.tangentMapOn_univ _) k)).symm.trans h

/-- `TΓ_Ψ` pulls `(TΓ_Ψ)_*(T(Γ^*Θ))` back to `T(Γ^*Θ)`. -/
theorem tangentThetaVia_obj {Θ : C.Obj → ℚ} (hΘ : S.IsBranchedSubcategory Θ)
    (v : (S.modelEpGroupoid Ψ).PObj.TangentSpace) :
    S.tangentThetaVia hU Ψ Θ (S.tangentModelObj hU Ψ v) = S.modelTangentTheta Ψ Θ v :=
  GroupoidFunctor.pushTheta_obj (tangentModelFunctor_full hU Ψ)
    (isFunctorial_modelTangentTheta hΘ) v

/-- `(TΓ_Ψ)_*(T(Γ^*Θ))(TΨ_λ(k)) = T(Θ ∘ Ψ_λ)(k)`. -/
theorem tangentThetaVia_tangentUnifObj {Θ : C.Obj → ℚ} (hΘ : S.IsBranchedSubcategory Θ) (i : ι)
    (k : (Ψ i).1.P.TangentSpace) :
    S.tangentThetaVia hU Ψ Θ (S.tangentUnifObj hU (Ψ i) k) =
      (Ψ i).1.ep.tangentTheta (Θ ∘ (Ψ i).1.obj) k := by
  have h := tangentThetaVia_obj hU hΘ (modelTObjMk Ψ i k)
  rw [tangentModelObj_mk, modelTangentTheta_mk hΘ] at h
  exact h

/-- **A covering subfamily gives the same push-forward**: for `Ψ ∘ σ` covering,
`(TΓ_{Ψ∘σ})_*(T(Γ_{Ψ∘σ}^*Θ)) = (TΓ_Ψ)_*(T(Γ_Ψ^*Θ))` (both are `T(Θ ∘ Ψ_λ)` on the summands). -/
theorem tangentThetaVia_eq_of_comp {κ : Type u} (σ : κ → ι) (hc : S.IsCoveringFamily (Ψ ∘ σ))
    {Θ : C.Obj → ℚ} (hΘ : S.IsBranchedSubcategory Θ) :
    S.tangentThetaVia hU (Ψ ∘ σ) Θ = S.tangentThetaVia hU Ψ Θ := by
  funext e
  obtain ⟨v, ψ, hs, ht⟩ := (GroupoidFunctor.essSurj_iff _).1 (tangentModelFunctor_essSurj hU hc) e
  obtain ⟨j, k, rfl⟩ := exists_modelTObjMk v
  have hs' : S.tangentCatGroupoid.src ψ = S.tangentUnifObj hU ((Ψ ∘ σ) j) k := by
    rw [hs, tangentModelFunctor_obj, tangentModelObj_mk]
  have h1 := GroupoidFunctor.pushTheta_eq (F := S.tangentModelFunctor hU (Ψ ∘ σ))
    (tangentModelFunctor_full hU _) (isFunctorial_modelTangentTheta hΘ) ⟨ψ, hs, ht⟩
  have h2 := GroupoidFunctor.pushTheta_eq (F := S.tangentModelFunctor hU Ψ)
    (x := modelTObjMk Ψ (σ j) k) (tangentModelFunctor_full hU _)
    (isFunctorial_modelTangentTheta hΘ)
    ⟨ψ, hs'.trans (by rw [tangentModelFunctor_obj, tangentModelObj_mk]; rfl), ht⟩
  change (S.tangentModelFunctor hU (Ψ ∘ σ)).pushTheta _ e =
    (S.tangentModelFunctor hU Ψ).pushTheta _ e
  rw [h1, h2, modelTangentTheta_mk hΘ, modelTangentTheta_mk hΘ]
  rfl

/-- **Definition 17.5.6, "this turns out not to be the case"** (2021 p. 815): the push-forward
`(TΓ)_*(T(Γ^*Θ))` does not depend on the covering family (through the union of the two). -/
theorem definition_17_5_6 {Θ : C.Obj → ℚ} (hΘ : S.IsBranchedSubcategory Θ)
    (c c' : S.CoveringFamily) : S.tangentThetaVia hU c.Ψ Θ = S.tangentThetaVia hU c'.Ψ Θ :=
  (tangentThetaVia_eq_of_comp hU (Ψ := (c.union c').Ψ) Sum.inl c.isCoveringFamily hΘ).trans
    (tangentThetaVia_eq_of_comp hU (Ψ := (c.union c').Ψ) Sum.inr c'.isCoveringFamily hΘ).symm

variable (S) in
/-- **The tangent `TΘ : TC → ℚ⁺` of `Θ`** (2021 Definition 17.5.6, p. 815):
`TΘ = (TΓ)_*(T(Γ^*Θ))`, here through the covering family `tangentCover hU`. -/
def branchedTangent (Θ : C.Obj → ℚ) : S.TangentCatObj → ℚ :=
  S.tangentThetaVia hU (S.tangentCover hU).Ψ Θ

/-- `TΘ = (TΓ)_*(T(Γ^*Θ))` for every covering family. -/
theorem branchedTangent_eq {Θ : C.Obj → ℚ} (hΘ : S.IsBranchedSubcategory Θ)
    (c : S.CoveringFamily) : S.branchedTangent hU Θ = S.tangentThetaVia hU c.Ψ Θ :=
  definition_17_5_6 hU hΘ _ c

/-- `(TΓ)^* TΘ = T(Γ^*Θ)` for every covering family. -/
theorem branchedTangent_comp_tangentModelObj {Θ : C.Obj → ℚ} (hΘ : S.IsBranchedSubcategory Θ)
    (c : S.CoveringFamily) :
    S.branchedTangent hU Θ ∘ S.tangentModelObj hU c.Ψ = S.modelTangentTheta c.Ψ Θ := by
  rw [branchedTangent_eq hU hΘ c]
  exact funext (tangentThetaVia_obj hU hΘ)

/-- **`TΘ(TΨ(k)) = T(Θ ∘ Ψ)(k)`** for every uniformizer `Ψ` of `F` (Chapter 9's tangent of the
branched ep⁺-subgroupoid `Θ ∘ Ψ`), through the covering family `tangentCover hU` together
with `Ψ`. -/
theorem branchedTangent_tangentUnifObj {Θ : C.Obj → ℚ} (hΘ : S.IsBranchedSubcategory Θ)
    (Ψ₀ : S.Unif) (k : Ψ₀.1.P.TangentSpace) :
    S.branchedTangent hU Θ (S.tangentUnifObj hU Ψ₀ k) =
      Ψ₀.1.ep.tangentTheta (Θ ∘ Ψ₀.1.obj) k := by
  let c := S.tangentCover hU
  let Φ : c.ι ⊕ PUnit.{u + 1} → S.Unif := Sum.elim c.Ψ fun _ => Ψ₀
  have h := tangentThetaVia_eq_of_comp hU (Ψ := Φ) Sum.inl c.isCoveringFamily hΘ
  change S.tangentThetaVia hU (Φ ∘ Sum.inl) Θ _ = _
  rw [h]
  exact tangentThetaVia_tangentUnifObj hU (Ψ := Φ) hΘ (Sum.inr PUnit.unit) k

theorem branchedTangent_nonneg (Θ : C.Obj → ℚ) (e : S.TangentCatObj) :
    0 ≤ S.branchedTangent hU Θ e :=
  GroupoidFunctor.pushTheta_nonneg (fun _ => EpGroupoid.tangentTheta_nonneg _ _) e

/-- `TΘ` is a functor `TC → ℚ⁺`. -/
theorem isFunctorial_branchedTangent {Θ : C.Obj → ℚ} (hΘ : S.IsBranchedSubcategory Θ) :
    (S.tangentGCT hU).toGroupoidStr.IsFunctorial (S.branchedTangent hU Θ) :=
  GroupoidFunctor.isFunctorial_pushTheta (tangentModelFunctor_full hU _)
    (isFunctorial_modelTangentTheta hΘ)

end TangentTheta

/-! ### `Gr(C)` -/

section GrC

open scoped Classical in
variable (S) in
/-- **`Tφ : T_αC → T_{α'}C`** for `φ : α → α'` (2021 p. 815): the target of the morphism
`(h̄, φ, Tφ(h̄))` of `TC` (Definition 17.2.6); the identity where that morphism is not defined. -/
def tcMove (φ : C.Mor) (e : S.TangentCatObj) : S.TangentCatObj :=
  if h : C.toGroupoidStr.src φ = e.base ∧ S.TangentObj (C.toGroupoidStr.tgt φ) then
    TangentCatMor.tgt ⟨e, φ, h.1, h.2⟩
  else e

theorem tcMove_eq (Φ : S.TangentCatMor) : S.tcMove Φ.mor Φ.src = Φ.tgt := by
  rw [tcMove, dif_pos ⟨Φ.src_eq, Φ.isObj_tgt⟩]

theorem tcMove_base {φ : C.Mor} {e : S.TangentCatObj} (hs : C.toGroupoidStr.src φ = e.base)
    (ht : S.TangentObj (C.toGroupoidStr.tgt φ)) :
    (S.tcMove φ e).base = C.toGroupoidStr.tgt φ := by
  rw [tcMove, dif_pos ⟨hs, ht⟩]
  rfl

/-- `Tφ' ∘ Tφ = T(φ' ∘ φ)`. -/
theorem tcMove_tcMove {φ φ' : C.Mor} {e : S.TangentCatObj} (hs : C.toGroupoidStr.src φ = e.base)
    (ht : S.TangentObj (C.toGroupoidStr.tgt φ))
    (hφ : C.toGroupoidStr.src φ' = C.toGroupoidStr.tgt φ)
    (ht' : S.TangentObj (C.toGroupoidStr.tgt φ')) :
    S.tcMove φ' (S.tcMove φ e) = S.tcMove (C.toGroupoidStr.comp φ' φ) e := by
  let Φ : S.TangentCatMor := ⟨e, φ, hs, ht⟩
  let Φ' : S.TangentCatMor := ⟨Φ.tgt, φ', hφ, ht'⟩
  have hm : C.toGroupoidStr.src Φ'.mor = C.toGroupoidStr.tgt Φ.mor := hφ
  have h1 : S.tcMove φ e = Φ.tgt := tcMove_eq Φ
  rw [h1]
  refine (tcMove_eq Φ').trans ?_
  rw [← TangentCatMor.tgt_comp Φ' Φ rfl, ← tcMove_eq (Φ'.comp Φ), TangentCatMor.comp_src hm,
    TangentCatMor.comp_mor hm]

theorem tangentObj_tgt_of_src (hU : S.HasUniformizers) {φ : C.Mor}
    (h : S.TangentObj (C.toGroupoidStr.src φ)) :
    S.TangentObj (C.toGroupoidStr.tgt φ) :=
  ⟨h.1.of_isomorphic ⟨φ, rfl, rfl⟩, hU _⟩

theorem tangentObj_src_of_tgt (hU : S.HasUniformizers) {φ : C.Mor}
    (h : S.TangentObj (C.toGroupoidStr.tgt φ)) :
    S.TangentObj (C.toGroupoidStr.src φ) :=
  ⟨h.1.of_isomorphic ⟨C.toGroupoidStr.inv φ, C.toGroupoidStr.src_inv φ,
    C.toGroupoidStr.tgt_inv φ⟩, hU _⟩

variable (S) in
/-- **`Gr(α)`** (2021 p. 815, `ν(α)`): finite formal sums `∑ σ_L · L`, `σ_L ∈ ℚ`, `σ_L ≥ 0`, of
subsets `L` of `T_αC` (the objects of `TC` over `α`; read as in Chapter 9's `EpGroupoid.Gr`). -/
def GrC (α : C.Obj) : Set (Set S.TangentCatObj →₀ ℚ) :=
  {w | (∀ L, 0 ≤ w L) ∧ ∀ L ∈ w.support, ∀ e ∈ L, e.base = α}

variable (S) in
/-- **`ν(φ)(∑ σ_L · L) = ∑ σ_L · φ_*L`**, `φ_*L = Tφ(L)` (2021 p. 815). -/
def grPushC (φ : C.Mor) (w : Set S.TangentCatObj →₀ ℚ) : Set S.TangentCatObj →₀ ℚ :=
  w.mapDomain (image (S.tcMove φ))

theorem grC_mapDomain_nonneg {α β : Type*} {w : α →₀ ℚ} (hw : ∀ a, 0 ≤ w a) (f : α → β)
    (b : β) : 0 ≤ w.mapDomain f b := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  refine Finset.sum_nonneg fun a _ => ?_
  dsimp only
  rw [Finsupp.single_apply]
  split_ifs
  · exact hw a
  · exact le_rfl

theorem grPushC_mem {φ : C.Mor} (ht : S.TangentObj (C.toGroupoidStr.tgt φ))
    {w : Set S.TangentCatObj →₀ ℚ} (hw : w ∈ S.GrC (C.toGroupoidStr.src φ)) :
    S.grPushC φ w ∈ S.GrC (C.toGroupoidStr.tgt φ) := by
  classical
  refine ⟨grC_mapDomain_nonneg hw.1 _, fun L hL e he => ?_⟩
  obtain ⟨L', hL', rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hL)
  obtain ⟨e', he', rfl⟩ := he
  exact tcMove_base (hw.2 L' hL' e' he').symm ht

/-- `ν(φ') ∘ ν(φ) = ν(φ' ∘ φ)`. -/
theorem grPushC_comp {φ φ' : C.Mor} (ht : S.TangentObj (C.toGroupoidStr.tgt φ))
    (hφ : C.toGroupoidStr.src φ' = C.toGroupoidStr.tgt φ)
    (ht' : S.TangentObj (C.toGroupoidStr.tgt φ')) {w : Set S.TangentCatObj →₀ ℚ}
    (hw : w ∈ S.GrC (C.toGroupoidStr.src φ)) :
    S.grPushC φ' (S.grPushC φ w) = S.grPushC (C.toGroupoidStr.comp φ' φ) w := by
  rw [grPushC, grPushC, grPushC, ← Finsupp.mapDomain_comp]
  refine Finsupp.mapDomain_congr fun L hL => ?_
  rw [Function.comp_apply, image_image]
  exact image_congr fun e he => tcMove_tcMove (hw.2 L hL e he).symm ht hφ ht'

end GrC

/-! ### Proposition 17.5.7: the section `TΘ` of `Gr(C) → C_∞` -/

section TangentSection

variable (hU : S.HasUniformizers) {ι : Type u} (Ψ : ι → S.Unif)

variable (S) in
/-- `Tφ ∘ TΓ_Ψ` on formal sums of subsets of `T_xX_Ψ`: `∑ σ_L · L ↦ ∑ σ_L · Tφ(TΓ(L))`. -/
def modelGrPush (φ : C.Mor) (w : Set (S.modelEpGroupoid Ψ).PObj.TangentSpace →₀ ℚ) :
    Set S.TangentCatObj →₀ ℚ :=
  w.mapDomain (image (S.tcMove φ ∘ S.tangentModelObj hU Ψ))

open scoped Classical in
variable (S) in
/-- **`TΓ_*(TΘ∘Γ)`** (2021 p. 816): at `α`, `Tφ(TΓ(TΓ^*Θ(x)))` for a chosen `x` and `φ : Γ(x) → α`
(`0` if there is none). -/
def tangentSectionVia (Θ : C.Obj → ℚ) (α : C.Obj) : Set S.TangentCatObj →₀ ℚ :=
  if h : ∃ x : S.ModelObj Ψ, ∃ φ : C.Mor,
      C.toGroupoidStr.src φ = (S.modelFunctor Ψ).obj x ∧ C.toGroupoidStr.tgt φ = α then
    S.modelGrPush hU Ψ h.choose_spec.choose
      ((S.modelEpGroupoid Ψ).tangentValue (S.modelPull Ψ Θ) h.choose)
  else 0

variable {Ψ}

theorem tangentModelObj_base (v : (S.modelEpGroupoid Ψ).PObj.TangentSpace) :
    (S.tangentModelObj hU Ψ v).base = (S.modelFunctor Ψ).obj
      ((S.modelEpGroupoid Ψ).PObj.levelVal 1 ((S.modelEpGroupoid Ψ).PObj.tangentProj v)) :=
  congrArg Subtype.val (tangentCatProj_tangentModelObj hU Ψ v)

/-- **`TΓ(Tψ(a)) = T(Γψ)(TΓ(a))`** for a morphism `ψ` of `X_Ψ` and `a ∈ T_{s ψ}X_Ψ` (`TΓ` is a
functor `TX → TC`). -/
theorem tangentModelObj_tangentMor {ψ : S.ModelMor Ψ}
    {a : (S.modelEpGroupoid Ψ).PObj.TangentSpace}
    (ha : (S.modelEpGroupoid Ψ).PObj.levelVal 1 ((S.modelEpGroupoid Ψ).PObj.tangentProj a) =
      (S.modelEpGroupoid Ψ).src ψ) :
    S.tangentModelObj hU Ψ ((S.modelEpGroupoid Ψ).tangentMor ψ a) =
      S.tcMove ((S.modelFunctor Ψ).mor ψ) (S.tangentModelObj hU Ψ a) := by
  have hψ : ψ ∈ (S.modelEpGroupoid Ψ).PMor.levelSet 1 :=
    ((S.modelEpGroupoid Ψ).mem_levelSet_src_iff ψ 1).1 (ha ▸ MPolyfold.levelVal_mem _)
  obtain ⟨W, rfl, rfl⟩ := (S.modelEpGroupoid Ψ).exists_tSrc_eq' hψ ha
  rw [(S.modelEpGroupoid Ψ).tangentMor_tSrc W]
  have h := tcMove_eq (S.tangentModelMor hU Ψ W)
  rw [tangentModelMor_src, tangentModelMor_tgt, tangentModelMor_mor] at h
  exact h.symm

variable {Θ : C.Obj → ℚ}

/-- **(17.86) and the independence of `(x, φ)`** (2021 p. 816): for `φ : Γ(x) → α` and
`φ' : Γ(x') → α`, `Tφ(TΓ(TΓ^*Θ(x))) = Tφ'(TΓ(TΓ^*Θ(x')))` (`Γ` is full, and `TΓ^*Θ` is natural,
Theorem 9.2.1 (2)). -/
theorem modelGrPush_tangentValue_eq (hΘ : S.IsBranchedSubcategory Θ) {α : C.Obj}
    (hα : S.TangentObj α) {x x' : S.ModelObj Ψ} {φ φ' : C.Mor}
    (hs : C.toGroupoidStr.src φ = (S.modelFunctor Ψ).obj x) (ht : C.toGroupoidStr.tgt φ = α)
    (hs' : C.toGroupoidStr.src φ' = (S.modelFunctor Ψ).obj x')
    (ht' : C.toGroupoidStr.tgt φ' = α) :
    S.modelGrPush hU Ψ φ ((S.modelEpGroupoid Ψ).tangentValue (S.modelPull Ψ Θ) x) =
      S.modelGrPush hU Ψ φ' ((S.modelEpGroupoid Ψ).tangentValue (S.modelPull Ψ Θ) x') := by
  have hinv : C.toGroupoidStr.src (C.toGroupoidStr.inv φ') = C.toGroupoidStr.tgt φ :=
    (C.toGroupoidStr.src_inv φ').trans (ht'.trans ht.symm)
  set χ := C.toGroupoidStr.comp (C.toGroupoidStr.inv φ') φ with hχ
  have hχs : C.toGroupoidStr.src χ = (S.modelFunctor Ψ).obj x :=
    (C.toGroupoidStr.src_comp _ _ hinv).trans hs
  have hχt : C.toGroupoidStr.tgt χ = (S.modelFunctor Ψ).obj x' :=
    (C.toGroupoidStr.tgt_comp _ _ hinv).trans ((C.toGroupoidStr.tgt_inv φ').trans hs')
  obtain ⟨ψ, rfl, rfl, hψ⟩ := (GroupoidFunctor.full_iff _).1 (S.modelFunctor_full Ψ) x x' χ hχs hχt
  have hT : S.TangentObj (C.toGroupoidStr.tgt χ) := by
    have h1 : S.TangentObj (C.toGroupoidStr.tgt φ') := by rw [ht']; exact hα
    have h2 := tangentObj_src_of_tgt hU h1
    rwa [hs', ← hχt] at h2
  have hcomp : C.toGroupoidStr.comp φ' χ = φ := by
    rw [hχ]
    have := C.toGroupoidStr.inv_comp_cancel_left (φ := C.toGroupoidStr.inv φ') (ψ := φ) hinv
    rwa [GroupoidStr.inv_inv] at this
  have hw := (S.modelEpGroupoid Ψ).tangentValue_mem (S.modelPull Ψ Θ) ((S.modelEpGroupoid Ψ).src ψ)
  change S.modelGrPush hU Ψ φ ((S.modelEpGroupoid Ψ).tangentValue (S.modelPull Ψ Θ)
      ((S.modelEpGroupoid Ψ).src ψ)) = S.modelGrPush hU Ψ φ'
    ((S.modelEpGroupoid Ψ).tangentValue (S.modelPull Ψ Θ) ((S.modelEpGroupoid Ψ).tgt ψ))
  rw [← (S.modelEpGroupoid Ψ).grPush_tangentValue hΘ.model
    ((S.modelEpGroupoid Ψ).hasIndependentTangentSums _) ψ]
  unfold modelGrPush EpGroupoid.grPush
  refine Eq.trans ?_ Finsupp.mapDomain_comp
  refine Finsupp.mapDomain_congr fun L hL => ?_
  rw [Function.comp_apply, image_image]
  refine image_congr fun a ha => ?_
  have hax := hw.2 L hL a ha
  rw [Function.comp_apply, Function.comp_apply, tangentModelObj_tangentMor hU hax, hψ,
    tcMove_tcMove ((tangentModelObj_base hU a).trans (congrArg _ hax) ▸ hχs) hT
      (hs'.trans hχt.symm) (ht' ▸ hα), hcomp]

theorem tangentSectionVia_eq (hΘ : S.IsBranchedSubcategory Θ) {α : C.Obj} (hα : S.TangentObj α)
    {x : S.ModelObj Ψ} {φ : C.Mor} (hs : C.toGroupoidStr.src φ = (S.modelFunctor Ψ).obj x)
    (ht : C.toGroupoidStr.tgt φ = α) :
    S.tangentSectionVia hU Ψ Θ α =
      S.modelGrPush hU Ψ φ ((S.modelEpGroupoid Ψ).tangentValue (S.modelPull Ψ Θ) x) := by
  have hex : ∃ x : S.ModelObj Ψ, ∃ φ : C.Mor,
      C.toGroupoidStr.src φ = (S.modelFunctor Ψ).obj x ∧ C.toGroupoidStr.tgt φ = α :=
    ⟨x, φ, hs, ht⟩
  rw [tangentSectionVia, dif_pos hex]
  exact modelGrPush_tangentValue_eq hU hΘ hα hex.choose_spec.choose_spec.1
    hex.choose_spec.choose_spec.2 hs ht

/-- `TΓ^*Θ` on a summand: `TΓ^*Θ(ι_λ q) = Tι_λ(T(Θ ∘ Ψ_λ)(q))`. -/
theorem tangentValue_model_mk (hΘ : S.IsBranchedSubcategory Θ) (i : ι) (q : (Ψ i).1.O) :
    (S.modelEpGroupoid Ψ).tangentValue (S.modelPull Ψ Θ) ⟨i, q⟩ =
      ((Ψ i).1.ep.tangentValue (Θ ∘ (Ψ i).1.obj) q).mapDomain (image (modelTObjMk Ψ i)) := by
  have hd := MPolyfold.isScDiffeoOn_sigmaMk (fun i => (Ψ i).1.P) i q
  by_cases hq : q ∈ EpGroupoid.supp (Θ ∘ (Ψ i).1.obj)
  · obtain ⟨B⟩ := (hΘ.unif (Ψ i)).localBranching _ hq
    rw [(Ψ i).1.ep.tangentValue_eq ((Ψ i).1.ep.hasIndependentTangentSums _) B,
      (S.modelEpGroupoid Ψ).tangentValue_eq ((S.modelEpGroupoid Ψ).hasIndependentTangentSums _)
        (B.mapDiffeo (Y := S.modelEpGroupoid Ψ) hd (mem_univ q) rfl (fun _ _ => rfl)),
      B.tangentSum_mapDiffeo (Y := S.modelEpGroupoid Ψ) hd (mem_univ q) rfl (fun _ _ => rfl)]
    exact congrArg (fun f => B.tangentSum.mapDomain (image f)) (MPolyfold.tangentMapOn_univ _)
  · have hq' : (⟨i, q⟩ : S.ModelObj Ψ) ∉ EpGroupoid.supp (S.modelPull Ψ Θ) := hq
    rw [(Ψ i).1.ep.tangentValue_eq_zero hq, (S.modelEpGroupoid Ψ).tangentValue_eq_zero hq']
    exact Finsupp.mapDomain_zero.symm

/-- **A covering subfamily gives the same section**: `TΓ_{Ψ∘σ *} T_{Θ∘Γ_{Ψ∘σ}} = TΓ_{Ψ *} T_{Θ∘Γ_Ψ}`
on `C¹`. -/
theorem tangentSectionVia_eq_of_comp {κ : Type u} (σ : κ → ι) (hc : S.IsCoveringFamily (Ψ ∘ σ))
    (hΘ : S.IsBranchedSubcategory Θ) {α : C.Obj} (hα : S.TangentObj α) :
    S.tangentSectionVia hU (Ψ ∘ σ) Θ α = S.tangentSectionVia hU Ψ Θ α := by
  obtain ⟨⟨j, q⟩, φ, hs, ht⟩ := (GroupoidFunctor.essSurj_iff _).1 (S.modelFunctor_essSurj hc) α
  rw [tangentSectionVia_eq hU hΘ hα hs ht,
    tangentSectionVia_eq hU (x := ⟨σ j, q⟩) hΘ hα hs ht, tangentValue_model_mk hΘ,
    tangentValue_model_mk hΘ]
  unfold modelGrPush
  refine Finsupp.mapDomain_comp.symm.trans (Eq.trans ?_ Finsupp.mapDomain_comp)
  refine Finsupp.mapDomain_congr fun L _ => ?_
  refine (image_image _ _ L).trans ((image_congr fun k _ => ?_).trans (image_image _ _ L).symm)
  change S.tcMove φ (S.tangentModelObj hU (Ψ ∘ σ) (modelTObjMk (Ψ ∘ σ) j k)) =
    S.tcMove φ (S.tangentModelObj hU Ψ (modelTObjMk Ψ (σ j) k))
  rw [tangentModelObj_mk, tangentModelObj_mk]
  rfl

/-- The section does not depend on the covering family (on `C¹`). -/
theorem tangentSectionVia_covering (hΘ : S.IsBranchedSubcategory Θ) (c c' : S.CoveringFamily)
    {α : C.Obj} (hα : S.TangentObj α) :
    S.tangentSectionVia hU c.Ψ Θ α = S.tangentSectionVia hU c'.Ψ Θ α :=
  (tangentSectionVia_eq_of_comp hU (Ψ := (c.union c').Ψ) Sum.inl c.isCoveringFamily hΘ hα).trans
    (tangentSectionVia_eq_of_comp hU (Ψ := (c.union c').Ψ) Sum.inr c'.isCoveringFamily hΘ hα).symm

theorem modelGrPush_mem {x : S.ModelObj Ψ} {φ : C.Mor}
    (hs : C.toGroupoidStr.src φ = (S.modelFunctor Ψ).obj x)
    (ht : S.TangentObj (C.toGroupoidStr.tgt φ))
    {w : Set (S.modelEpGroupoid Ψ).PObj.TangentSpace →₀ ℚ} (hw : w ∈ (S.modelEpGroupoid Ψ).Gr x) :
    S.modelGrPush hU Ψ φ w ∈ S.GrC (C.toGroupoidStr.tgt φ) := by
  classical
  refine ⟨grC_mapDomain_nonneg hw.1 _, fun L hL e he => ?_⟩
  obtain ⟨L', hL', rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hL)
  obtain ⟨a, ha, rfl⟩ := he
  exact tcMove_base (hs.trans ((congrArg _ (hw.2 L' hL' a ha)).symm.trans
    (tangentModelObj_base hU a).symm)) ht

/-- `ν(χ) ∘ (Tφ ∘ TΓ) = T(χ ∘ φ) ∘ TΓ` on `Gr(x)`. -/
theorem grPushC_modelGrPush {x : S.ModelObj Ψ} {φ χ : C.Mor}
    (hs : C.toGroupoidStr.src φ = (S.modelFunctor Ψ).obj x)
    (ht : S.TangentObj (C.toGroupoidStr.tgt φ))
    (hχ : C.toGroupoidStr.src χ = C.toGroupoidStr.tgt φ)
    (ht' : S.TangentObj (C.toGroupoidStr.tgt χ))
    {w : Set (S.modelEpGroupoid Ψ).PObj.TangentSpace →₀ ℚ} (hw : w ∈ (S.modelEpGroupoid Ψ).Gr x) :
    S.grPushC χ (S.modelGrPush hU Ψ φ w) =
      S.modelGrPush hU Ψ (C.toGroupoidStr.comp χ φ) w := by
  rw [grPushC, modelGrPush, modelGrPush, ← Finsupp.mapDomain_comp]
  refine Finsupp.mapDomain_congr fun L hL => ?_
  rw [Function.comp_apply, image_image]
  refine image_congr fun a ha => ?_
  exact tcMove_tcMove (hs.trans ((congrArg _ (hw.2 L hL a ha)).symm.trans
    (tangentModelObj_base hU a).symm)) ht hχ ht'

variable (S) in
/-- **The section `TΘ` of `Gr(C) → C_∞`** (2021 Proposition 17.5.7, p. 816), through the covering
family `tangentCover hU`. -/
def branchedTangentSection (Θ : C.Obj → ℚ) : C.Obj → Set S.TangentCatObj →₀ ℚ :=
  S.tangentSectionVia hU (S.tangentCover hU).Ψ Θ

/-- **Proposition 17.5.7** (2021 p. 816): for a branched ep⁺-subcategory `Θ`, `TΘ` is a section
of `Gr(C) → C_∞`: (1) `TΘ(α) ∈ Gr(α)` for `α ∈ C¹`; (2) `TΘ = TΓ_* T_{Θ∘Γ}` for every covering
family, i.e. `TΘ(α) = Tφ(TΓ(TΓ^*Θ(x)))` for every `x` and `φ : Γ(x) → α`; (3) `TΘ` is a functor:
`TΘ(α') = ν(χ)(TΘ(α))` for `χ : α → α'`; and (4) `TΘ` is uniquely determined by (2) for one
covering family. -/
theorem proposition_17_5_7 (hΘ : S.IsBranchedSubcategory Θ) :
    (∀ α, S.TangentObj α → S.branchedTangentSection hU Θ α ∈ S.GrC α) ∧
    (∀ (c : S.CoveringFamily) (α : C.Obj), S.TangentObj α → ∀ (x : S.ModelObj c.Ψ) (φ : C.Mor),
      C.toGroupoidStr.src φ = (S.modelFunctor c.Ψ).obj x → C.toGroupoidStr.tgt φ = α →
      S.branchedTangentSection hU Θ α =
        S.modelGrPush hU c.Ψ φ ((S.modelEpGroupoid c.Ψ).tangentValue (S.modelPull c.Ψ Θ) x)) ∧
    (∀ χ : C.Mor, S.TangentObj (C.toGroupoidStr.tgt χ) →
      S.branchedTangentSection hU Θ (C.toGroupoidStr.tgt χ) =
        S.grPushC χ (S.branchedTangentSection hU Θ (C.toGroupoidStr.src χ))) ∧
    (∀ (c : S.CoveringFamily) (T : C.Obj → Set S.TangentCatObj →₀ ℚ),
      (∀ α, S.TangentObj α → ∀ (x : S.ModelObj c.Ψ) (φ : C.Mor),
        C.toGroupoidStr.src φ = (S.modelFunctor c.Ψ).obj x → C.toGroupoidStr.tgt φ = α →
        T α = S.modelGrPush hU c.Ψ φ
          ((S.modelEpGroupoid c.Ψ).tangentValue (S.modelPull c.Ψ Θ) x)) →
      ∀ α, S.TangentObj α → T α = S.branchedTangentSection hU Θ α) := by
  have h2 : ∀ (c : S.CoveringFamily) (α : C.Obj), S.TangentObj α →
      ∀ (x : S.ModelObj c.Ψ) (φ : C.Mor),
      C.toGroupoidStr.src φ = (S.modelFunctor c.Ψ).obj x → C.toGroupoidStr.tgt φ = α →
      S.branchedTangentSection hU Θ α =
        S.modelGrPush hU c.Ψ φ ((S.modelEpGroupoid c.Ψ).tangentValue (S.modelPull c.Ψ Θ) x) :=
    fun c α hα x φ hs ht =>
      (tangentSectionVia_covering hU hΘ _ c hα).trans (tangentSectionVia_eq hU hΘ hα hs ht)
  have hex : ∀ α, ∃ x : S.ModelObj (S.tangentCover hU).Ψ, ∃ φ : C.Mor,
      C.toGroupoidStr.src φ = (S.modelFunctor _).obj x ∧ C.toGroupoidStr.tgt φ = α := fun α =>
    (GroupoidFunctor.essSurj_iff _).1
      (S.modelFunctor_essSurj (S.tangentCover hU).isCoveringFamily) α
  refine ⟨fun α hα => ?_, h2, fun χ hχ => ?_, fun c T hT α hα => ?_⟩
  · obtain ⟨x, φ, hs, ht⟩ := hex α
    rw [h2 _ α hα x φ hs ht, ← ht]
    exact modelGrPush_mem hU hs (ht ▸ hα)
      ((S.modelEpGroupoid _).tangentValue_mem _ x)
  · obtain ⟨x, φ, hs, ht⟩ := hex (C.toGroupoidStr.src χ)
    have hα : S.TangentObj (C.toGroupoidStr.src χ) := tangentObj_src_of_tgt hU hχ
    have hc : C.toGroupoidStr.src χ = C.toGroupoidStr.tgt φ := ht.symm
    rw [h2 _ _ hα x φ hs ht, grPushC_modelGrPush hU hs (ht ▸ hα) hc hχ
      ((S.modelEpGroupoid _).tangentValue_mem _ x)]
    exact h2 _ _ hχ x _ ((C.toGroupoidStr.src_comp _ _ hc).trans hs)
      (C.toGroupoidStr.tgt_comp _ _ hc)
  · obtain ⟨x, φ, hs, ht⟩ := (GroupoidFunctor.essSurj_iff _).1
      (S.modelFunctor_essSurj c.isCoveringFamily) α
    rw [hT α hα x φ hs ht, h2 c α hα x φ hs ht]

end TangentSection

/-! ### Definition 17.5.8: orientations -/

section Orientation

variable (S) in
/-- **An oriented subset `L̂` of `T_αC`** (2021 p. 816): a dimension `n`, a set `L` of objects of
`TC` and the set of its positively oriented frames `(h̄₁, …, h̄ₙ) ∈ Lⁿ` (Chapter 9's
`MPolyfold.OrTangent`, read on the fibres of `TC`). -/
structure OrTC where
  /-- The dimension `n`. -/
  dim : ℕ
  /-- The underlying set `L`. -/
  carrier : Set S.TangentCatObj
  /-- The positively oriented frames. -/
  frames : Set (Fin dim → S.TangentCatObj)

variable (S) in
/-- **`Gr̂(α)`** (2021 p. 817): finite formal sums `∑ σ_L̂ · L̂`, `σ_L̂ ∈ ℚ`, `σ_L̂ ≥ 0`, of
oriented subsets of `T_αC` (frames in `L`). -/
def GrHatC (α : C.Obj) : Set (S.OrTC →₀ ℚ) :=
  {w | (∀ g, 0 ≤ w g) ∧ ∀ g ∈ w.support, (∀ e ∈ g.carrier, e.base = α) ∧
    ∀ v ∈ g.frames, ∀ i, v i ∈ g.carrier}

variable (S) in
/-- **The forgetful functor `f : Gr̂(C) → Gr(C)`** (17.87): `∑ σ_L̂ · L̂ ↦ ∑ σ_L̂ · L`. -/
def grForgetC (w : S.OrTC →₀ ℚ) : Set S.TangentCatObj →₀ ℚ := w.mapDomain OrTC.carrier

variable (S) in
/-- `Tφ(L̂)`: the image of the set and of the frames. -/
def OrTC.move (φ : C.Mor) (g : S.OrTC) : S.OrTC :=
  ⟨g.dim, S.tcMove φ '' g.carrier, (fun v => S.tcMove φ ∘ v) '' g.frames⟩

variable (S) in
/-- The action `∑ σ_L̂ · L̂ ↦ ∑ σ_L̂ · Tφ(L̂)` of a morphism on `Gr̂(C)`. -/
def grHatPushC (φ : C.Mor) (w : S.OrTC →₀ ℚ) : S.OrTC →₀ ℚ := w.mapDomain (OrTC.move S φ)

variable (hU : S.HasUniformizers) {ι : Type u} (Ψ : ι → S.Unif)

variable (S) in
/-- The preimage of `L̂ ⊂ T_{Γ(x)}C` under `TΓ(x) : T_xX → T_{Γ(x)}C`. -/
def orTCPull (x : S.ModelObj Ψ) (g : S.OrTC) : (S.modelEpGroupoid Ψ).PObj.OrTangent :=
  ⟨g.dim, {a | (S.modelEpGroupoid Ψ).PObj.levelVal 1 ((S.modelEpGroupoid Ψ).PObj.tangentProj a) =
      x ∧ S.tangentModelObj hU Ψ a ∈ g.carrier},
    {v | (∀ i, (S.modelEpGroupoid Ψ).PObj.levelVal 1
      ((S.modelEpGroupoid Ψ).PObj.tangentProj (v i)) = x) ∧
      S.tangentModelObj hU Ψ ∘ v ∈ g.frames}⟩

variable (S) in
/-- **The pull-back `TΓ^*T̂`** (2021 p. 817): `(TΓ^*T̂)(x) = TΓ(x)⁻¹(T̂(Γ(x)))`, the preimages of
the oriented subsets of `T̂(Γ(x))` under `TΓ(x)`. -/
def sectionPull (T : C.Obj → S.OrTC →₀ ℚ) (x : S.ModelObj Ψ) :
    (S.modelEpGroupoid Ψ).PObj.OrTangent →₀ ℚ :=
  (T ((S.modelFunctor Ψ).obj x)).mapDomain (S.orTCPull hU Ψ x)

variable (S) in
/-- **Definition 17.5.8** (2021 p. 817): an **orientation** of the branched ep⁺-subcategory `Θ`
is a section functor `T̂Θ` of `Gr̂(C) → C_∞` (`T̂Θ(α) ∈ Gr̂(α)`, `T̂Θ(t χ) = Tχ(T̂Θ(s χ))`) with
`f ∘ T̂Θ = TΘ`, such that for a covering family `Ψ` with `Γ : X → C` the pull-back `TΓ^*T̂Θ` is an
orientation of `Γ^*Θ` in the sense of Definition 9.3.2.  We read "for a covering set" as "for
every covering family". -/
structure IsOrientationC (Θ : C.Obj → ℚ) (T : C.Obj → S.OrTC →₀ ℚ) : Prop where
  mem : ∀ α, S.IsSmoothObj α → T α ∈ S.GrHatC α
  natural : ∀ χ : C.Mor, S.IsSmoothObj (C.toGroupoidStr.src χ) →
    T (C.toGroupoidStr.tgt χ) = S.grHatPushC χ (T (C.toGroupoidStr.src χ))
  lifts : ∀ α, S.IsSmoothObj α → S.grForgetC (T α) = S.branchedTangentSection hU Θ α
  pull : ∀ c : S.CoveringFamily,
    (S.modelEpGroupoid c.Ψ).IsOrientation (S.modelPull c.Ψ Θ) (S.sectionPull hU c.Ψ T)

/-- `TΘ = 0` for `Θ = 0`. -/
theorem branchedTangentSection_zero (α : C.Obj) :
    S.branchedTangentSection hU (0 : C.Obj → ℚ) α = 0 := by
  classical
  unfold branchedTangentSection tangentSectionVia
  split_ifs with h
  · rw [(S.modelEpGroupoid _).tangentValue_eq_zero (fun h' => lt_irrefl (0 : ℚ) h'), modelGrPush]
    exact Finsupp.mapDomain_zero
  · rfl

/-- **Satisfiability of Definition 17.5.8**: `T̂ = 0` is an orientation of `Θ = 0`. -/
theorem isOrientationC_zero : S.IsOrientationC hU (0 : C.Obj → ℚ) fun _ => 0 where
  mem α _ := ⟨fun _ => le_rfl, fun g hg => by simp at hg⟩
  natural χ _ := by rw [grHatPushC, Finsupp.mapDomain_zero]
  lifts α _ := by rw [grForgetC, Finsupp.mapDomain_zero, branchedTangentSection_zero]
  pull c := by
    have h : S.sectionPull hU c.Ψ (fun _ => (0 : S.OrTC →₀ ℚ)) = fun _ => 0 :=
      funext fun x => Finsupp.mapDomain_zero
    rw [h]
    exact (S.modelEpGroupoid c.Ψ).isOrientation_zero

end Orientation

end GCT.PolyfoldConstruction

end Polyfold
