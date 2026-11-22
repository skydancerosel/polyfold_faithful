import Polyfold.Chapter17.TangentTransition
import Polyfold.Chapter17.LevelStructures

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.2 (pp. 776–781): **Proposition 17.2.14** (metrizability, the inversion, the unit and the
multiplication) and **Proposition 17.2.15**.  Numbers and pages are the 2021 text's.

# The natural M-polyfold structure of `M(TΨ₁, TΨ₂)`

## The text, paraphrased

(**Proposition 17.2.14**, pp. 776–781) The natural topology on `M(TΨ₁, TΨ₂)` is metrizable; `s`
and `t` are local homeomorphisms, `ι` is a homeomorphism, `u` and `m` are continuous ("we leave
the details to the reader").  Metrizability is proved through the Nagata–Smirnov theorem:
Hausdorff, locally metrizable, locally complete, completely regular and paracompact, the last by
a locally finite closed cover pulled back along `P : M(TΨ₁, TΨ₂) → M(Ψ₁, Ψ₂)¹`.
(**Proposition 17.2.15**, p. 781) `M(TΨ, TΨ')` carries a natural M-polyfold structure, the maps
(17.42) `k ↦ (k, Φ_k, Tσ(k))` being charts with transition maps the identities; `s`, `t` are
local sc-diffeomorphisms, `ι` an sc-diffeomorphism, `u` and `m` sc-smooth ("we leave the details
to the reader").

## What is formalized (namespace `Polyfold.GCT.PolyfoldConstruction`)

* `trTSrc`, `trTTgt`, `trBase` (`Ts`, `Tt` and the base point on Part I's tangent `TM(Ψ₁, Ψ₂)`),
  `trTTgt_eq_transMap` (`Tt = Tσ ∘ Ts`, `σ` of the base point).
* `TTr.ext'` (an element of `M(TΨ₁, TΨ₂)` is determined by its source and its morphism of `C`).
* **The identification `TM(Ψ₁, Ψ₂) ≃ M(TΨ₁, TΨ₂)`**, `v ↦ (Ts v, (TΨ₁(Ts v), p(v), ·), Tt v)`:
  `tangentTrMap`, `tangentTrMap_eq_chart` (on a sheet it is the map (17.42) composed with `Ts`),
  `tangentTrMap_lift` (the map (17.42) is `Ts⁻¹` followed by it), `tangentTrEquiv`.
* `TTrM hU Ψ₁ Ψ₂` (`M(TΨ₁, TΨ₂)` with the natural topology of Definition 17.2.13),
  **`tangentTrHomeomorph`** (the identification is a homeomorphism for the natural topology),
  `metrizableSpace_TTrM`.
* `tangentTrPolyfold` (**the natural M-polyfold structure**, transported from Part I's `TM(Ψ₁, Ψ₂)`),
  `isScDiffeoOn_tangentTrChartExt` (the maps (17.42) are sc-diffeomorphisms onto open sets: they are
  the charts of the structure), Definition 17.1.8 (a)–(c) for `M(TΨ, TΨ')`:
  `tangentTr_isLocalScDiffeo_src`, `_tgt`, `tangentTr_isScSmoothMap_unit`, `_inv`,
  `tangentTr_isScDiffeoOn_inv`, `tangentTr_isScSmoothMap_mul` (through the local criterion
  `MPolyfold.isScSmoothOnFibredProduct_of_local`).
* **`proposition_17_2_14`**, **`proposition_17_2_15`**.

## Readings and proof

* The natural topology is T5's `tangentTrTopology` (the final topology of the maps (17.42)).  We do
  not follow the text's Nagata–Smirnov argument: the map `v ↦ (Ts v, Φ, Tt v)` is a bijection of
  Part I's tangent `TM(Ψ₁, Ψ₂)` onto `M(TΨ₁, TΨ₂)` which, on the sheet of an admissible triple, is
  the map (17.42) composed with the sc-diffeomorphism `Ts`.  So it is a homeomorphism for the
  natural topology, and `M(TΨ₁, TΨ₂)` is metrizable because `TM(Ψ₁, Ψ₂)` is (Part I).
* "Natural M-polyfold structure" is read as the structure for which the maps (17.42) are
  sc-diffeomorphisms onto open sets; we take the transport of Part I's `T M(Ψ₁, Ψ₂)` and prove that
  the maps (17.42) are its charts.  Under the identification, `s`, `t`, `u`, `ι` are `Ts`, `Tt`,
  `Tu`, `Tι`, and the multiplication is, near a point, `T` of the sheet map
  `b ↦ m(σ(t b), b)` composed with `pr₂`.
* Continuity of `ι`, `u`, `m` (Proposition 17.2.14) follows from their sc-smoothness, the
  topology underlying the M-polyfold being the natural topology.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} {S : C.PolyfoldConstruction}

/-! ### `Ts`, `Tt` on Part I's tangent `TM(Ψ₁, Ψ₂)` -/

section Tangent

variable {Ψ₁ Ψ₂ : S.Unif}

variable (S) in
/-- `Ts : TM(Ψ₁, Ψ₂) → TO₁`, Part I's tangent of the source map. -/
abbrev trTSrc (Ψ₁ Ψ₂ : S.Unif) :
    (S.transPolyfold Ψ₁ Ψ₂).TangentSpace → Ψ₁.1.P.TangentSpace :=
  MPolyfold.tangentMap (S.isLocalScDiffeo_trSrc Ψ₁ Ψ₂).isScSmoothMap

variable (S) in
/-- `Tt : TM(Ψ₁, Ψ₂) → TO₂`, Part I's tangent of the target map. -/
abbrev trTTgt (Ψ₁ Ψ₂ : S.Unif) :
    (S.transPolyfold Ψ₁ Ψ₂).TangentSpace → Ψ₂.1.P.TangentSpace :=
  MPolyfold.tangentMap (S.isLocalScDiffeo_trTgt Ψ₁ Ψ₂).isScSmoothMap

/-- The base point `p(v) ∈ M(Ψ₁, Ψ₂)¹` of `v ∈ TM(Ψ₁, Ψ₂)`. -/
abbrev trBase (v : (S.transPolyfold Ψ₁ Ψ₂).TangentSpace) : S.Tr Ψ₁ Ψ₂ :=
  (S.transPolyfold Ψ₁ Ψ₂).levelVal 1 ((S.transPolyfold Ψ₁ Ψ₂).tangentProj v)

theorem basePt_trTSrc (v : (S.transPolyfold Ψ₁ Ψ₂).TangentSpace) :
    basePt Ψ₁ (S.trTSrc Ψ₁ Ψ₂ v) = (trBase v).src :=
  MPolyfold.levelVal_tangentProj_tangentMap _ v

theorem basePt_trTTgt (v : (S.transPolyfold Ψ₁ Ψ₂).TangentSpace) :
    basePt Ψ₂ (S.trTTgt Ψ₁ Ψ₂ v) = (trBase v).tgt :=
  MPolyfold.levelVal_tangentProj_tangentMap _ v

/-- **`Tt = Tσ ∘ Ts` on a sheet**: on `U(o, φ, o')`, `t = σ ∘ s`. -/
theorem trTTgt_eq_tangentMapOn {o : S.Tr Ψ₁ Ψ₂} (T : S.AdmissibleTriple o)
    {v : (S.transPolyfold Ψ₁ Ψ₂).TangentSpace} (hv : trBase v ∈ T.carrier) :
    S.trTTgt Ψ₁ Ψ₂ v = MPolyfold.tangentMapOn T.isScSmoothOn_sigma (S.trTSrc Ψ₁ Ψ₂ v) := by
  have hs := (S.isLocalScDiffeo_trSrc Ψ₁ Ψ₂).isScSmoothMap
  have ht := (S.isLocalScDiffeo_trTgt Ψ₁ Ψ₂).isScSmoothMap
  have hv' : v ∈ (S.transPolyfold Ψ₁ Ψ₂).tangentPreimage T.carrier := hv
  have heq : EqOn (T.sigma ∘ fun b : S.Tr Ψ₁ Ψ₂ => b.src) (fun b : S.Tr Ψ₁ Ψ₂ => b.tgt)
      T.carrier := fun b hb => T.sigma_eq hb
  rw [MPolyfold.tangentMapOn_tangentMap T.isScSmoothOn_sigma hs T.isOpen_carrier
      T.isScDiffeoOn_src.mapsTo hv',
    MPolyfold.tangentMapOn_congr _ (ht.mono T.isOpen_carrier (subset_univ _)) T.isOpen_carrier
      subset_rfl subset_rfl heq hv',
    MPolyfold.tangentMapOn_eq_tangentMap ht _ hv']

/-- **`Tt(v) = Tσ(Ts(v))`** for `σ` of the base point of `v`. -/
theorem trTTgt_eq_transMap (v : (S.transPolyfold Ψ₁ Ψ₂).TangentSpace) :
    S.trTTgt Ψ₁ Ψ₂ v = S.transMap (trBase v) (S.trTSrc Ψ₁ Ψ₂ v) :=
  trTTgt_eq_tangentMapOn (S.triple _) (S.triple _).mem_carrier

end Tangent

variable (S) in
/-- **`M(TΨ₁, TΨ₂)` with the natural topology** (Definition 17.2.13), a type synonym of `TTr`
carrying the topology and the M-polyfold structure of Propositions 17.2.14 and 17.2.15. -/
def TTrM (hU : S.HasUniformizers) (Ψ₁ Ψ₂ : S.Unif) : Type (max u 1) := S.TTr hU Ψ₁ Ψ₂

/-! ### The identification `TM(Ψ₁, Ψ₂) ≃ M(TΨ₁, TΨ₂)` -/

section Identification

variable {hU : S.HasUniformizers} {Ψ₁ Ψ₂ : S.Unif}

/-- **An element of `M(TΨ₁, TΨ₂)` is determined by its source `k` and its morphism `φ` of `C`**
(the source of `Φ` is `TΨ₁(k)`, its target `TΨ₂(k')` determines `k'`). -/
theorem TTr.ext' {x y : S.TTr hU Ψ₁ Ψ₂} (h₁ : x.src = y.src) (h₂ : x.mor.mor = y.mor.mor) :
    x = y := by
  have hm : x.mor = y.mor :=
    TangentCatMor.ext' (x.src_mor.trans ((congrArg _ h₁).trans y.src_mor.symm)) h₂
  refine GroupoidStr.TransitionSet.ext h₁ hm (injective_tangentUnifObj hU Ψ₂ ?_)
  exact x.tgt_mor.symm.trans ((congrArg S.tangentCatGroupoid.tgt hm).trans y.tgt_mor)

theorem trTSrc_mem (v : (S.transPolyfold Ψ₁ Ψ₂).TangentSpace) {o : S.Tr Ψ₁ Ψ₂}
    (T : S.AdmissibleTriple o) (hv : trBase v ∈ T.carrier) :
    S.trTSrc Ψ₁ Ψ₂ v ∈ Ψ₁.1.P.tangentPreimage T.srcSet := by
  change basePt Ψ₁ (S.trTSrc Ψ₁ Ψ₂ v) ∈ T.srcSet
  rw [basePt_trTSrc]
  exact T.isScDiffeoOn_src.mapsTo hv

variable (hU) in
/-- **`TM(Ψ₁, Ψ₂) → M(TΨ₁, TΨ₂)`**, `v ↦ (Ts v, (TΨ₁(Ts v), p(v), ·), Tt v)`: the map (17.42) of
the chosen admissible triple of `p(v)`, at `Ts v`. -/
def tangentTrMap (v : (S.transPolyfold Ψ₁ Ψ₂).TangentSpace) : S.TTr hU Ψ₁ Ψ₂ :=
  S.tangentTrChart hU (S.triple (trBase v))
    ⟨S.trTSrc Ψ₁ Ψ₂ v, trTSrc_mem v _ (S.triple _).mem_carrier⟩

@[simp] theorem tangentTrMap_src (v : (S.transPolyfold Ψ₁ Ψ₂).TangentSpace) :
    (tangentTrMap hU v).src = S.trTSrc Ψ₁ Ψ₂ v := rfl

theorem tangentTrMap_mor (v : (S.transPolyfold Ψ₁ Ψ₂).TangentSpace) :
    (tangentTrMap hU v).mor.mor = (trBase v).mor := by
  change ((S.triple (trBase v)).srcInv (basePt Ψ₁ (S.trTSrc Ψ₁ Ψ₂ v))).mor = _
  rw [basePt_trTSrc, (S.triple _).srcInv_eq (S.triple _).mem_carrier]

theorem tangentTrMap_tgt (v : (S.transPolyfold Ψ₁ Ψ₂).TangentSpace) :
    (tangentTrMap hU v).tgt = S.trTTgt Ψ₁ Ψ₂ v :=
  (tangentTrChart_tgt hU _ _).trans (trTTgt_eq_transMap v).symm

/-- On the sheet of any admissible triple `T`, the identification is the map (17.42) of `T` at
`Ts v`. -/
theorem tangentTrMap_eq_chart {o : S.Tr Ψ₁ Ψ₂} (T : S.AdmissibleTriple o)
    {v : (S.transPolyfold Ψ₁ Ψ₂).TangentSpace} (hv : trBase v ∈ T.carrier) :
    tangentTrMap hU v = S.tangentTrChart hU T ⟨S.trTSrc Ψ₁ Ψ₂ v, trTSrc_mem v T hv⟩ := by
  refine TTr.ext' rfl ?_
  rw [tangentTrMap_mor, tangentTrChart_mor]
  change _ = (T.srcInv (basePt Ψ₁ (S.trTSrc Ψ₁ Ψ₂ v))).mor
  rw [basePt_trTSrc, T.srcInv_eq hv]

theorem injective_tangentTrMap : Injective (tangentTrMap hU (Ψ₁ := Ψ₁) (Ψ₂ := Ψ₂)) := by
  intro v w h
  have hs : S.trTSrc Ψ₁ Ψ₂ v = S.trTSrc Ψ₁ Ψ₂ w := congrArg GroupoidStr.TransitionSet.src h
  have hm : (trBase v).mor = (trBase w).mor := by
    rw [← tangentTrMap_mor (hU := hU), ← tangentTrMap_mor (hU := hU), h]
  have ht : S.trTTgt Ψ₁ Ψ₂ v = S.trTTgt Ψ₁ Ψ₂ w := by
    rw [← tangentTrMap_tgt (hU := hU), h, tangentTrMap_tgt]
  have hb : trBase v = trBase w := GroupoidStr.TransitionSet.ext
    (by rw [← basePt_trTSrc, hs, basePt_trTSrc]) hm (by rw [← basePt_trTTgt, ht, basePt_trTTgt])
  have hp : (S.transPolyfold Ψ₁ Ψ₂).tangentProj v = (S.transPolyfold Ψ₁ Ψ₂).tangentProj w :=
    MPolyfold.level_ext hb
  exact (S.isLocalScDiffeo_trSrc Ψ₁ Ψ₂).injOn_tangentFiber _ hp rfl hs

variable {o : S.Tr Ψ₁ Ψ₂}

/-- `(Ts|TU(o, φ, o'))⁻¹ : TU(o) → TU(o, φ, o')`. -/
abbrev tangentLift (T : S.AdmissibleTriple o) :
    Ψ₁.1.P.TangentSpace → (S.transPolyfold Ψ₁ Ψ₂).TangentSpace :=
  MPolyfold.tangentMapOn T.isScDiffeoOn_src.isScSmoothOn_inv

theorem isScDiffeoOn_tangentLift (T : S.AdmissibleTriple o) :
    Ψ₁.1.P.tangentPolyfold.IsScDiffeoOn (S.transPolyfold Ψ₁ Ψ₂).tangentPolyfold
      (tangentLift T) (S.trTSrc Ψ₁ Ψ₂) (Ψ₁.1.P.tangentPreimage T.srcSet)
      ((S.transPolyfold Ψ₁ Ψ₂).tangentPreimage T.carrier) :=
  (T.isScDiffeoOn_src.tangentMap (S.isLocalScDiffeo_trSrc Ψ₁ Ψ₂).isScSmoothMap).symm

theorem trBase_tangentLift_mem (T : S.AdmissibleTriple o) {k : Ψ₁.1.P.TangentSpace}
    (hk : k ∈ Ψ₁.1.P.tangentPreimage T.srcSet) : trBase (tangentLift T k) ∈ T.carrier :=
  (isScDiffeoOn_tangentLift T).mapsTo hk

theorem trTSrc_tangentLift (T : S.AdmissibleTriple o) {k : Ψ₁.1.P.TangentSpace}
    (hk : k ∈ Ψ₁.1.P.tangentPreimage T.srcSet) : S.trTSrc Ψ₁ Ψ₂ (tangentLift T k) = k :=
  (isScDiffeoOn_tangentLift T).left_inv k hk

/-- **The map (17.42) is `Ts⁻¹` followed by the identification.** -/
theorem tangentTrMap_lift (T : S.AdmissibleTriple o) (k : Ψ₁.1.P.tangentPreimage T.srcSet) :
    tangentTrMap hU (tangentLift T k.1) = S.tangentTrChart hU T k :=
  (tangentTrMap_eq_chart T (trBase_tangentLift_mem T k.2)).trans
    (congrArg _ (Subtype.ext (trTSrc_tangentLift T k.2)))

theorem surjective_tangentTrMap : Surjective (tangentTrMap hU (Ψ₁ := Ψ₁) (Ψ₂ := Ψ₂)) := by
  intro x
  obtain ⟨o, T, k, -, rfl⟩ := lemma_17_2_11_one hU x
  exact ⟨_, tangentTrMap_lift T k⟩

variable (hU Ψ₁ Ψ₂) in
/-- **`TM(Ψ₁, Ψ₂) ≃ M(TΨ₁, TΨ₂)`** as a bijection. -/
def tangentTrEquiv : (S.transPolyfold Ψ₁ Ψ₂).TangentSpace ≃ S.TTrM hU Ψ₁ Ψ₂ :=
  Equiv.ofBijective _ ⟨injective_tangentTrMap, surjective_tangentTrMap⟩

theorem tangentTrEquiv_symm_chart (T : S.AdmissibleTriple o)
    (k : Ψ₁.1.P.tangentPreimage T.srcSet) :
    (tangentTrEquiv hU Ψ₁ Ψ₂).symm (S.tangentTrChart hU T k) = tangentLift T k.1 :=
  (Equiv.symm_apply_eq _).2 (tangentTrMap_lift T k).symm

end Identification

/-! ### `M(TΨ₁, TΨ₂)` with the natural topology -/

section Natural

variable {hU : S.HasUniformizers} {Ψ₁ Ψ₂ Ψ₃ : S.Unif}

instance (hU : S.HasUniformizers) (Ψ₁ Ψ₂ : S.Unif) : TopologicalSpace (S.TTrM hU Ψ₁ Ψ₂) :=
  S.tangentTrTopology hU Ψ₁ Ψ₂

/-- An element of `M(TΨ₁, TΨ₂)` as an element of `TTrM`. -/
abbrev toTTrM (x : S.TTr hU Ψ₁ Ψ₂) : S.TTrM hU Ψ₁ Ψ₂ := x

theorem isOpenEmbedding_tangentTrChart {o : S.Tr Ψ₁ Ψ₂} (T : S.AdmissibleTriple o) :
    @IsOpenEmbedding _ (S.TTrM hU Ψ₁ Ψ₂) _ _ (S.tangentTrChart hU T) :=
  (proposition_17_2_12 hU Ψ₁ Ψ₂).1 T

/-- The inverse of the identification is a local homeomorphism: composed with a map (17.42) it
is `(Ts|TU(o, φ, o'))⁻¹`, an open embedding. -/
theorem isLocalHomeomorph_tangentTrEquiv_symm :
    IsLocalHomeomorph fun x : S.TTrM hU Ψ₁ Ψ₂ => (tangentTrEquiv hU Ψ₁ Ψ₂).symm x := by
  refine isLocalHomeomorph_of_comp_tangentTrChart hU _ fun {o} T => ?_
  have hemb := (isScDiffeoOn_tangentLift (Ψ₂ := Ψ₂) T).toOpenPartialHomeomorph.isOpenEmbedding_restrict
  convert hemb using 1 <;> first
    | rfl
    | exact heq_of_eq (funext fun k => tangentTrEquiv_symm_chart T k)

variable (hU Ψ₁ Ψ₂) in
/-- **The identification `TM(Ψ₁, Ψ₂) ≃ₜ M(TΨ₁, TΨ₂)` is a homeomorphism** for the natural
topology. -/
def tangentTrHomeomorph : (S.transPolyfold Ψ₁ Ψ₂).TangentSpace ≃ₜ S.TTrM hU Ψ₁ Ψ₂ :=
  (Equiv.toHomeomorphOfContinuousOpen (tangentTrEquiv hU Ψ₁ Ψ₂).symm
    isLocalHomeomorph_tangentTrEquiv_symm.continuous
    isLocalHomeomorph_tangentTrEquiv_symm.isOpenMap).symm

@[simp] theorem tangentTrHomeomorph_apply (v : (S.transPolyfold Ψ₁ Ψ₂).TangentSpace) :
    tangentTrHomeomorph hU Ψ₁ Ψ₂ v = tangentTrMap hU v := rfl

instance (hU : S.HasUniformizers) (Ψ₁ Ψ₂ : S.Unif) : T2Space (S.TTrM hU Ψ₁ Ψ₂) :=
  (tangentTrHomeomorph hU Ψ₁ Ψ₂).symm.isEmbedding.t2Space

instance (hU : S.HasUniformizers) (Ψ₁ Ψ₂ : S.Unif) : ParacompactSpace (S.TTrM hU Ψ₁ Ψ₂) :=
  (tangentTrHomeomorph hU Ψ₁ Ψ₂).symm.isClosedEmbedding.paracompactSpace

/-- **`M(TΨ₁, TΨ₂)` is metrizable** (Proposition 17.2.14): it is homeomorphic to Part I's
`TM(Ψ₁, Ψ₂)`. -/
instance metrizableSpace_TTrM (hU : S.HasUniformizers) (Ψ₁ Ψ₂ : S.Unif) :
    TopologicalSpace.MetrizableSpace (S.TTrM hU Ψ₁ Ψ₂) :=
  have := (S.transPolyfold Ψ₁ Ψ₂).metrizableSpace_tangentSpace
  (tangentTrHomeomorph hU Ψ₁ Ψ₂).symm.isEmbedding.metrizableSpace

variable (S hU Ψ₁ Ψ₂) in
/-- **The natural M-polyfold structure of `M(TΨ₁, TΨ₂)`** (Proposition 17.2.15): Part I's
`TM(Ψ₁, Ψ₂)` transported along the identification (its charts are the maps (17.42),
`isScDiffeoOn_tangentTrChartExt`). -/
def tangentTrPolyfold : MPolyfold (S.TTrM hU Ψ₁ Ψ₂) :=
  (S.transPolyfold Ψ₁ Ψ₂).tangentPolyfold.transport (tangentTrHomeomorph hU Ψ₁ Ψ₂)

theorem isScDiffeoOn_tangentTrHomeomorph :
    (S.transPolyfold Ψ₁ Ψ₂).tangentPolyfold.IsScDiffeoOn (S.tangentTrPolyfold hU Ψ₁ Ψ₂)
      (tangentTrHomeomorph hU Ψ₁ Ψ₂) (tangentTrHomeomorph hU Ψ₁ Ψ₂).symm univ univ :=
  MPolyfold.isScDiffeoOn_transport _ _

theorem isLocalScDiffeo_tangentTrHomeomorph_symm :
    (S.tangentTrPolyfold hU Ψ₁ Ψ₂).IsLocalScDiffeo (S.transPolyfold Ψ₁ Ψ₂).tangentPolyfold
      (tangentTrHomeomorph hU Ψ₁ Ψ₂).symm := fun _ =>
  ⟨univ, univ, tangentTrHomeomorph hU Ψ₁ Ψ₂, mem_univ _,
    isScDiffeoOn_tangentTrHomeomorph.symm⟩

theorem isScSmoothMap_tangentTrHomeomorph :
    (S.transPolyfold Ψ₁ Ψ₂).tangentPolyfold.IsScSmoothMap (S.tangentTrPolyfold hU Ψ₁ Ψ₂)
      (tangentTrHomeomorph hU Ψ₁ Ψ₂) :=
  isScDiffeoOn_tangentTrHomeomorph.isScSmoothOn

/-! ### The maps (17.42) are the charts -/

variable (hU) in
/-- The map (17.42) of `T` extended to all of `TO₁`: `Ts⁻¹` on `TU(o)` followed by the
identification (outside `TU(o)` a value without meaning). -/
abbrev tangentTrChartExt {o : S.Tr Ψ₁ Ψ₂} (T : S.AdmissibleTriple o) :
    Ψ₁.1.P.TangentSpace → S.TTrM hU Ψ₁ Ψ₂ :=
  tangentTrHomeomorph hU Ψ₁ Ψ₂ ∘ tangentLift T

theorem tangentTrChartExt_eq {o : S.Tr Ψ₁ Ψ₂} (T : S.AdmissibleTriple o)
    (k : Ψ₁.1.P.tangentPreimage T.srcSet) :
    tangentTrChartExt hU T k.1 = S.tangentTrChart hU T k :=
  show tangentTrMap hU (tangentLift T k.1) = _ from tangentTrMap_lift T k

/-- **The maps (17.42) are charts of the natural M-polyfold structure** (Proposition 17.2.15):
`k ↦ (k, Φ_k, Tσ(k))` is an sc-diffeomorphism of `TU(o)` onto an open subset of `M(TΨ₁, TΨ₂)`,
with inverse `s`. -/
theorem isScDiffeoOn_tangentTrChartExt {o : S.Tr Ψ₁ Ψ₂} (T : S.AdmissibleTriple o) :
    Ψ₁.1.P.tangentPolyfold.IsScDiffeoOn (S.tangentTrPolyfold hU Ψ₁ Ψ₂) (tangentTrChartExt hU T)
      (fun x : S.TTrM hU Ψ₁ Ψ₂ => x.src) (Ψ₁.1.P.tangentPreimage T.srcSet)
      (univ ∩ (tangentTrHomeomorph hU Ψ₁ Ψ₂).symm ⁻¹'
        (S.transPolyfold Ψ₁ Ψ₂).tangentPreimage T.carrier) := by
  have h1 := (isScDiffeoOn_tangentTrHomeomorph (hU := hU) (Ψ₁ := Ψ₁) (Ψ₂ := Ψ₂)).restrict
    (MPolyfold.isOpen_tangentPreimage T.isOpen_carrier) (subset_univ _)
  refine ((h1.comp (isScDiffeoOn_tangentLift T)).congr_right fun x _ => ?_)
  change S.trTSrc Ψ₁ Ψ₂ ((tangentTrHomeomorph hU Ψ₁ Ψ₂).symm x) = x.src
  conv_rhs => rw [← (tangentTrHomeomorph hU Ψ₁ Ψ₂).apply_symm_apply x]
  rfl

/-! ### Definition 17.1.8 (a)–(c) for `M(TΨ, TΨ')` -/

theorem src_eq_trTSrc (x : S.TTrM hU Ψ₁ Ψ₂) :
    x.src = S.trTSrc Ψ₁ Ψ₂ ((tangentTrHomeomorph hU Ψ₁ Ψ₂).symm x) := by
  conv_lhs => rw [← (tangentTrHomeomorph hU Ψ₁ Ψ₂).apply_symm_apply x]
  rfl

theorem tgt_eq_trTTgt (x : S.TTrM hU Ψ₁ Ψ₂) :
    x.tgt = S.trTTgt Ψ₁ Ψ₂ ((tangentTrHomeomorph hU Ψ₁ Ψ₂).symm x) := by
  conv_lhs => rw [← (tangentTrHomeomorph hU Ψ₁ Ψ₂).apply_symm_apply x]
  exact tangentTrMap_tgt _

theorem mor_eq_trBase (x : S.TTrM hU Ψ₁ Ψ₂) :
    x.mor.mor = (trBase ((tangentTrHomeomorph hU Ψ₁ Ψ₂).symm x)).mor := by
  conv_lhs => rw [← (tangentTrHomeomorph hU Ψ₁ Ψ₂).apply_symm_apply x]
  exact tangentTrMap_mor _

/-- **Definition 17.1.8 (a) for `M(TΨ₁, TΨ₂)`**: `s` is a local sc-diffeomorphism (it is `Ts`). -/
theorem tangentTr_isLocalScDiffeo_src :
    (S.tangentTrPolyfold hU Ψ₁ Ψ₂).IsLocalScDiffeo Ψ₁.1.P.tangentPolyfold
      fun x : S.TTrM hU Ψ₁ Ψ₂ => x.src := by
  have h : (fun x : S.TTrM hU Ψ₁ Ψ₂ => x.src) =
      S.trTSrc Ψ₁ Ψ₂ ∘ (tangentTrHomeomorph hU Ψ₁ Ψ₂).symm := funext src_eq_trTSrc
  rw [h]
  exact (S.isLocalScDiffeo_trSrc Ψ₁ Ψ₂).tangentMap.comp isLocalScDiffeo_tangentTrHomeomorph_symm

/-- **Definition 17.1.8 (a) for `M(TΨ₁, TΨ₂)`**: `t` is a local sc-diffeomorphism (it is `Tt`). -/
theorem tangentTr_isLocalScDiffeo_tgt :
    (S.tangentTrPolyfold hU Ψ₁ Ψ₂).IsLocalScDiffeo Ψ₂.1.P.tangentPolyfold
      fun x : S.TTrM hU Ψ₁ Ψ₂ => x.tgt := by
  have h : (fun x : S.TTrM hU Ψ₁ Ψ₂ => x.tgt) =
      S.trTTgt Ψ₁ Ψ₂ ∘ (tangentTrHomeomorph hU Ψ₁ Ψ₂).symm := funext tgt_eq_trTTgt
  rw [h]
  exact (S.isLocalScDiffeo_trTgt Ψ₁ Ψ₂).tangentMap.comp isLocalScDiffeo_tangentTrHomeomorph_symm

/-- `Tu : TO → TM(Ψ, Ψ)`, Part I's tangent of the unit map. -/
abbrev trTUnit (Ψ : S.Unif) : Ψ.1.P.TangentSpace → (S.transPolyfold Ψ Ψ).TangentSpace :=
  MPolyfold.tangentMap (S.isScSmoothMap_trUnit Ψ)

/-- Under the identification the unit map of `M(TΨ, TΨ)` is `Tu`. -/
theorem tangentTrMap_trTUnit (Ψ : S.Unif) (k : Ψ.1.P.TangentSpace) :
    tangentTrMap hU (trTUnit Ψ k) = GroupoidStr.TransitionSet.unit k := by
  refine TTr.ext' ?_ ?_
  · exact MPolyfold.tangentMap_tangentMap_of_eq_id _ _ rfl k
  · rw [tangentTrMap_mor, trBase, MPolyfold.levelVal_tangentProj_tangentMap]
    rfl

/-- **Definition 17.1.8 (b) for `M(TΨ, TΨ)`**: the unit map `TO → M(TΨ, TΨ)` is sc-smooth (it is
`Tu`). -/
theorem tangentTr_isScSmoothMap_unit (Ψ : S.Unif) :
    Ψ.1.P.tangentPolyfold.IsScSmoothMap (S.tangentTrPolyfold hU Ψ Ψ)
      fun k => toTTrM (hU := hU) (GroupoidStr.TransitionSet.unit k) := by
  have h : (fun k => toTTrM (hU := hU) (GroupoidStr.TransitionSet.unit k)) =
      tangentTrHomeomorph hU Ψ Ψ ∘ trTUnit Ψ := funext fun k => (tangentTrMap_trTUnit Ψ k).symm
  rw [h]
  exact isScSmoothMap_tangentTrHomeomorph.comp (MPolyfold.tangentMap_isScSmooth _)

/-- `Tι : TM(Ψ₁, Ψ₂) → TM(Ψ₂, Ψ₁)`, Part I's tangent of the inversion. -/
abbrev trTInv (Ψ₁ Ψ₂ : S.Unif) :
    (S.transPolyfold Ψ₁ Ψ₂).TangentSpace → (S.transPolyfold Ψ₂ Ψ₁).TangentSpace :=
  MPolyfold.tangentMap (S.isScSmoothMap_trInv Ψ₁ Ψ₂)

/-- Under the identification the inversion of `M(TΨ₁, TΨ₂)` is `Tι`. -/
theorem tangentTrMap_trTInv (v : (S.transPolyfold Ψ₁ Ψ₂).TangentSpace) :
    tangentTrMap hU (trTInv Ψ₁ Ψ₂ v) = GroupoidStr.TransitionSet.inv (tangentTrMap hU v) := by
  refine TTr.ext' ?_ ?_
  · change S.trTSrc Ψ₂ Ψ₁ (trTInv Ψ₁ Ψ₂ v) = (tangentTrMap hU v).tgt
    rw [tangentTrMap_tgt]
    exact MPolyfold.tangentMap_tangentMap_of_eq _ _ _ rfl v
  · rw [tangentTrMap_mor, trBase, MPolyfold.levelVal_tangentProj_tangentMap]
    change C.toGroupoidStr.inv (trBase v).mor = C.toGroupoidStr.inv (tangentTrMap hU v).mor.mor
    rw [tangentTrMap_mor]

theorem tangentTr_inv_eq :
    (fun x : S.TTrM hU Ψ₁ Ψ₂ => toTTrM (hU := hU) (GroupoidStr.TransitionSet.inv x)) =
      tangentTrHomeomorph hU Ψ₂ Ψ₁ ∘ trTInv Ψ₁ Ψ₂ ∘ (tangentTrHomeomorph hU Ψ₁ Ψ₂).symm := by
  funext x
  conv_lhs => rw [← (tangentTrHomeomorph hU Ψ₁ Ψ₂).apply_symm_apply x]
  exact (tangentTrMap_trTInv _).symm

/-- **Definition 17.1.8 (b) for `M(TΨ₁, TΨ₂)`**: the inversion is sc-smooth (it is `Tι`). -/
theorem tangentTr_isScSmoothMap_inv :
    (S.tangentTrPolyfold hU Ψ₁ Ψ₂).IsScSmoothMap (S.tangentTrPolyfold hU Ψ₂ Ψ₁)
      fun x : S.TTrM hU Ψ₁ Ψ₂ => toTTrM (hU := hU) (GroupoidStr.TransitionSet.inv x) := by
  rw [tangentTr_inv_eq]
  exact isScSmoothMap_tangentTrHomeomorph.comp ((MPolyfold.tangentMap_isScSmooth _).comp
    isLocalScDiffeo_tangentTrHomeomorph_symm.isScSmoothMap)

/-- **The inversion `M(TΨ₁, TΨ₂) → M(TΨ₂, TΨ₁)` is an sc-diffeomorphism** (Proposition 17.2.15). -/
theorem tangentTr_isScDiffeoOn_inv :
    (S.tangentTrPolyfold hU Ψ₁ Ψ₂).IsScDiffeoOn (S.tangentTrPolyfold hU Ψ₂ Ψ₁)
      (fun x : S.TTrM hU Ψ₁ Ψ₂ => toTTrM (hU := hU) (GroupoidStr.TransitionSet.inv x))
      (fun x : S.TTrM hU Ψ₂ Ψ₁ => toTTrM (hU := hU) (GroupoidStr.TransitionSet.inv x))
      univ univ :=
  ⟨tangentTr_isScSmoothMap_inv, tangentTr_isScSmoothMap_inv, mapsTo_univ _ _, mapsTo_univ _ _,
    fun x _ => GroupoidStr.TransitionSet.inv_inv x, fun x _ => GroupoidStr.TransitionSet.inv_inv x⟩

/-- **Definition 17.1.8 (c) for `M(TΨ, TΨ')`**: the multiplication
`M(TΨ₂, TΨ₃) ₛ×ₜ M(TΨ₁, TΨ₂) → M(TΨ₁, TΨ₃)` is sc-smooth.  Near a point it is
`T(b ↦ m(σ(t b), b))` (Definition 17.1.8 (c) for `M` on a sheet `σ` of `s`) composed with `pr₂`. -/
theorem tangentTr_isScSmoothMap_mul :
    MPolyfold.IsScSmoothOnFibredProduct (S.tangentTrPolyfold hU Ψ₂ Ψ₃)
      (S.tangentTrPolyfold hU Ψ₁ Ψ₂) (S.tangentTrPolyfold hU Ψ₁ Ψ₃)
      tangentTr_isLocalScDiffeo_src tangentTr_isLocalScDiffeo_tgt.isScSmoothMap
      fun p => toTTrM (hU := hU) (GroupoidStr.TransitionSet.mul p) := by
  classical
  refine MPolyfold.isScSmoothOnFibredProduct_of_local _ _ fun a₀ => ?_
  set E₁ := tangentTrHomeomorph hU Ψ₂ Ψ₃
  set E₂ := tangentTrHomeomorph hU Ψ₁ Ψ₂
  set E₃ := tangentTrHomeomorph hU Ψ₁ Ψ₃
  have hbase : ∀ p : MPolyfold.fibredProduct (fun x : S.TTrM hU Ψ₂ Ψ₃ => x.src)
      (fun x : S.TTrM hU Ψ₁ Ψ₂ => x.tgt),
      (trBase (E₁.symm p.1.1)).src = (trBase (E₂.symm p.1.2)).tgt := fun p => by
    have h : p.1.1.src = p.1.2.tgt := p.2
    rw [src_eq_trTSrc, tgt_eq_trTTgt] at h
    rw [← basePt_trTSrc, ← basePt_trTTgt]
    exact congrArg (basePt Ψ₂) h
  obtain ⟨U, V, σ, hU₀, hd⟩ := S.isLocalScDiffeo_trSrc Ψ₂ Ψ₃ (trBase (E₁.symm a₀.1.1))
  have hg₀ := (S.isLocalScDiffeo_trTgt Ψ₁ Ψ₂).isScSmoothMap
  let _ := MPolyfold.paracompactSpace_prod (S.transPolyfold Ψ₂ Ψ₃) (S.transPolyfold Ψ₁ Ψ₂)
  let p₀ : MPolyfold.fibredProduct (fun a : S.Tr Ψ₂ Ψ₃ => a.src)
      (fun a : S.Tr Ψ₁ Ψ₂ => a.tgt) := ⟨(trBase (E₁.symm a₀.1.1), trBase (E₂.symm a₀.1.2)),
    hbase a₀⟩
  let d := MPolyfold.fibredSubDataL hd hg₀
  let r : S.Tr Ψ₁ Ψ₂ → MPolyfold.fibredProduct (fun a : S.Tr Ψ₂ Ψ₃ => a.src)
      (fun a : S.Tr Ψ₁ Ψ₂ => a.tgt) := fun b => d.retractInto p₀ (σ b.tgt, b)
  have hr : ∀ b : S.Tr Ψ₁ Ψ₂, b.tgt ∈ V → (r b : S.Tr Ψ₂ Ψ₃ × S.Tr Ψ₁ Ψ₂) = (σ b.tgt, b) :=
    fun b hb => d.retractInto_val p₀ ⟨hd.mapsTo_inv hb, hb⟩
  let k₀ : S.Tr Ψ₁ Ψ₂ → S.Tr Ψ₁ Ψ₃ := fun b => S.toTr (GroupoidStr.TransitionSet.mul (r b))
  have hk₀ : (S.transPolyfold Ψ₁ Ψ₂).IsScSmoothOn (S.transPolyfold Ψ₁ Ψ₃) k₀
      ((fun b : S.Tr Ψ₁ Ψ₂ => b.tgt) ⁻¹' V) :=
    (S.isScSmoothMap_trMul Ψ₁ Ψ₂ Ψ₃).isScSmoothOn_sheet hd p₀
  have hk₀src : ∀ b : S.Tr Ψ₁ Ψ₂, b.tgt ∈ V → (k₀ b).src = b.src := fun b hb =>
    congrArg (fun q : S.Tr Ψ₂ Ψ₃ × S.Tr Ψ₁ Ψ₂ => q.2.src) (hr b hb)
  have hk₀mor : ∀ b : S.Tr Ψ₁ Ψ₂, b.tgt ∈ V →
      (k₀ b).mor = C.toGroupoidStr.comp (σ b.tgt).mor b.mor := fun b hb =>
    congrArg (fun q : S.Tr Ψ₂ Ψ₃ × S.Tr Ψ₁ Ψ₂ => C.toGroupoidStr.comp q.1.mor q.2.mor) (hr b hb)
  have hV : IsOpen ((fun b : S.Tr Ψ₁ Ψ₂ => b.tgt) ⁻¹' V) := hk₀.isOpen
  let W : Set (S.TTrM hU Ψ₁ Ψ₂) :=
    E₂.symm ⁻¹' (S.transPolyfold Ψ₁ Ψ₂).tangentPreimage ((fun b : S.Tr Ψ₁ Ψ₂ => b.tgt) ⁻¹' V)
  have hWo : IsOpen W := (MPolyfold.isOpen_tangentPreimage hV).preimage E₂.symm.continuous
  refine ⟨{p | E₁.symm p.1 ∈ (S.transPolyfold Ψ₂ Ψ₃).tangentPreimage U ∧ p.2 ∈ W}, W,
    E₃ ∘ MPolyfold.tangentMapOn hk₀ ∘ E₂.symm,
    ((MPolyfold.isOpen_tangentPreimage hd.isOpen_source).preimage
      (E₁.symm.continuous.comp continuous_fst)).inter (hWo.preimage continuous_snd),
    ⟨hU₀, ?_⟩, ?_, fun p hp => ⟨hp.2, ?_⟩⟩
  · change (trBase (E₂.symm a₀.1.2)).tgt ∈ V
    rw [← hbase a₀]
    exact hd.mapsTo hU₀
  · exact MPolyfold.IsScSmoothOn.comp isScSmoothMap_tangentTrHomeomorph
      (MPolyfold.IsScSmoothOn.comp (MPolyfold.tangentMapOn_isScSmoothOn hk₀)
        (isLocalScDiffeo_tangentTrHomeomorph_symm.isScSmoothMap.mono hWo (subset_univ _))
        fun x hx => hx) (mapsTo_univ _ _)
  · set v := E₂.symm p.1.2
    have hv : v ∈ (S.transPolyfold Ψ₁ Ψ₂).tangentPreimage
        ((fun b : S.Tr Ψ₁ Ψ₂ => b.tgt) ⁻¹' V) := hp.2
    have hσ : σ (trBase v).tgt = trBase (E₁.symm p.1.1) := by
      rw [← hbase p]
      exact hd.left_inv _ hp.1
    have hbv : trBase (MPolyfold.tangentMapOn hk₀ v) = k₀ (trBase v) :=
      MPolyfold.levelVal_tangentProj_tangentMapOn hk₀ hv
    refine TTr.ext' ?_ ?_
    · change p.1.2.src = (tangentTrMap hU (MPolyfold.tangentMapOn hk₀ v)).src
      rw [tangentTrMap_src, src_eq_trTSrc]
      exact (MPolyfold.tangentMap_tangentMapOn_of_eqOn hk₀ _ _
        (fun b hb => hk₀src b hb) hv).symm
    · have hm := TangentCatMor.mor_composable (show p.1.1.mor.src = p.1.2.mor.tgt from
        (p.1.1.src_mor.trans ((congrArg (S.tangentUnifObj hU Ψ₂) p.2).trans
          p.1.2.tgt_mor.symm)))
      change (TangentCatMor.comp p.1.1.mor p.1.2.mor).mor =
        (tangentTrMap hU (MPolyfold.tangentMapOn hk₀ v)).mor.mor
      rw [TangentCatMor.comp_mor hm, tangentTrMap_mor, hbv, hk₀mor _ hv, hσ, mor_eq_trBase,
        mor_eq_trBase]

/-! ### The projection `M(TΨ₁, TΨ₂) → M(Ψ₁, Ψ₂)¹` -/

variable (hU) in
/-- **The canonical map `P : M(TΨ₁, TΨ₂) → M(Ψ₁, Ψ₂)¹`** (2021 pp. 780, 781),
`(k, (TΨ₁(k), φ, TΨ₂(k')), k') ↦ (τ(k), φ, τ'(k'))`: the tangent projection under the
identification. -/
abbrev tangentTrProj (x : S.TTrM hU Ψ₁ Ψ₂) : (S.transPolyfold Ψ₁ Ψ₂).Level 1 :=
  (S.transPolyfold Ψ₁ Ψ₂).tangentProj ((tangentTrHomeomorph hU Ψ₁ Ψ₂).symm x)

/-- `P(k, Φ, k') = (τ(k), φ, τ'(k'))`: the source entry. -/
theorem tangentTrProj_src (x : S.TTrM hU Ψ₁ Ψ₂) :
    ((S.transPolyfold Ψ₁ Ψ₂).levelVal 1 (tangentTrProj hU x)).src = basePt Ψ₁ x.src := by
  rw [src_eq_trTSrc, basePt_trTSrc]

/-- `P(k, Φ, k') = (τ(k), φ, τ'(k'))`: the morphism entry. -/
theorem tangentTrProj_mor (x : S.TTrM hU Ψ₁ Ψ₂) :
    ((S.transPolyfold Ψ₁ Ψ₂).levelVal 1 (tangentTrProj hU x)).mor = x.mor.mor :=
  (mor_eq_trBase x).symm

/-- `P(k, Φ, k') = (τ(k), φ, τ'(k'))`: the target entry. -/
theorem tangentTrProj_tgt (x : S.TTrM hU Ψ₁ Ψ₂) :
    ((S.transPolyfold Ψ₁ Ψ₂).levelVal 1 (tangentTrProj hU x)).tgt = basePt Ψ₂ x.tgt := by
  rw [tgt_eq_trTTgt, basePt_trTTgt]

/-- **`P : M(TΨ₁, TΨ₂) → M(Ψ₁, Ψ₂)¹` is sc-smooth** (2021 p. 781, "in suitable local coordinates it
takes the form `k ↦ τ(k)`"). -/
theorem isScSmoothMap_tangentTrProj :
    (S.tangentTrPolyfold hU Ψ₁ Ψ₂).IsScSmoothMap (S.transPolyfold Ψ₁ Ψ₂).shift
      (tangentTrProj hU (Ψ₁ := Ψ₁) (Ψ₂ := Ψ₂)) :=
  (S.transPolyfold Ψ₁ Ψ₂).tangentProj_isScSmooth.comp
    isLocalScDiffeo_tangentTrHomeomorph_symm.isScSmoothMap

end Natural

/-! ### Propositions 17.2.14 and 17.2.15 -/

/-- **Proposition 17.2.14** (2021 pp. 776–781): the natural topology on `M(TΨ₁, TΨ₂)` is
metrizable, `s` and `t` are local homeomorphisms, the inversion is a homeomorphism, and the unit
and multiplication maps are continuous. -/
theorem proposition_17_2_14 (hU : S.HasUniformizers) (Ψ₁ Ψ₂ Ψ₃ : S.Unif) :
    TopologicalSpace.MetrizableSpace (S.TTrM hU Ψ₁ Ψ₂) ∧
      IsLocalHomeomorph (fun x : S.TTrM hU Ψ₁ Ψ₂ => x.src) ∧
      IsLocalHomeomorph (fun x : S.TTrM hU Ψ₁ Ψ₂ => x.tgt) ∧
      IsHomeomorph (fun x : S.TTrM hU Ψ₁ Ψ₂ => toTTrM (hU := hU) (GroupoidStr.TransitionSet.inv x)) ∧
      Continuous (fun k : Ψ₁.1.P.TangentSpace =>
        toTTrM (hU := hU) (GroupoidStr.TransitionSet.unit k : S.TTr hU Ψ₁ Ψ₁)) ∧
      Continuous (fun p : MPolyfold.fibredProduct (fun x : S.TTrM hU Ψ₂ Ψ₃ => x.src)
          (fun x : S.TTrM hU Ψ₁ Ψ₂ => x.tgt) =>
        toTTrM (hU := hU) (GroupoidStr.TransitionSet.mul p)) := by
  have hι := (tangentTr_isScDiffeoOn_inv (hU := hU) (Ψ₁ := Ψ₁) (Ψ₂ := Ψ₂))
  refine ⟨inferInstance, (proposition_17_2_14_src_tgt hU Ψ₁ Ψ₂).1,
    (proposition_17_2_14_src_tgt hU Ψ₁ Ψ₂).2, ?_, ?_, ?_⟩
  · exact (Homeomorph.mk (Equiv.mk
        (fun x : S.TTrM hU Ψ₁ Ψ₂ => toTTrM (hU := hU) (GroupoidStr.TransitionSet.inv x))
        (fun x : S.TTrM hU Ψ₂ Ψ₁ => toTTrM (hU := hU) (GroupoidStr.TransitionSet.inv x))
        (fun x => GroupoidStr.TransitionSet.inv_inv x)
        (fun x => GroupoidStr.TransitionSet.inv_inv x))
      (continuousOn_univ.1 hι.isScSmoothOn.continuousOn)
      (continuousOn_univ.1 hι.isScSmoothOn_inv.continuousOn)).isHomeomorph
  · exact continuousOn_univ.1 (tangentTr_isScSmoothMap_unit Ψ₁).continuousOn
  · let _ := MPolyfold.paracompactSpace_prod (S.tangentTrPolyfold hU Ψ₂ Ψ₃)
      (S.tangentTrPolyfold hU Ψ₁ Ψ₂)
    let _ := ((S.tangentTrPolyfold hU Ψ₂ Ψ₃).prod (S.tangentTrPolyfold hU Ψ₁ Ψ₂)).paracompactSpace_subtype
      (MPolyfold.fibredProduct (fun x : S.TTrM hU Ψ₂ Ψ₃ => x.src)
        (fun x : S.TTrM hU Ψ₁ Ψ₂ => x.tgt))
    exact continuousOn_univ.1 (tangentTr_isScSmoothMap_mul (hU := hU) (Ψ₁ := Ψ₁) (Ψ₂ := Ψ₂)
      (Ψ₃ := Ψ₃)).continuousOn

/-- **Proposition 17.2.15** (2021 p. 781): the natural M-polyfold structure on `M(TΨ₁, TΨ₂)`:
the maps (17.42) are charts (sc-diffeomorphisms of `TU(o)` onto open sets, with inverse `s`),
`s` and `t` are local sc-diffeomorphisms, the inversion is an sc-diffeomorphism, and the unit and
multiplication maps are sc-smooth. -/
theorem proposition_17_2_15 (hU : S.HasUniformizers) (Ψ₁ Ψ₂ Ψ₃ : S.Unif) :
    (∀ {o : S.Tr Ψ₁ Ψ₂} (T : S.AdmissibleTriple o),
      (∀ k : Ψ₁.1.P.tangentPreimage T.srcSet, tangentTrChartExt hU T k.1 = S.tangentTrChart hU T k) ∧
      Ψ₁.1.P.tangentPolyfold.IsScDiffeoOn (S.tangentTrPolyfold hU Ψ₁ Ψ₂) (tangentTrChartExt hU T)
        (fun x : S.TTrM hU Ψ₁ Ψ₂ => x.src) (Ψ₁.1.P.tangentPreimage T.srcSet)
        (univ ∩ (tangentTrHomeomorph hU Ψ₁ Ψ₂).symm ⁻¹'
          (S.transPolyfold Ψ₁ Ψ₂).tangentPreimage T.carrier)) ∧
      (S.tangentTrPolyfold hU Ψ₁ Ψ₂).IsLocalScDiffeo Ψ₁.1.P.tangentPolyfold
        (fun x : S.TTrM hU Ψ₁ Ψ₂ => x.src) ∧
      (S.tangentTrPolyfold hU Ψ₁ Ψ₂).IsLocalScDiffeo Ψ₂.1.P.tangentPolyfold
        (fun x : S.TTrM hU Ψ₁ Ψ₂ => x.tgt) ∧
      (S.tangentTrPolyfold hU Ψ₁ Ψ₂).IsScDiffeoOn (S.tangentTrPolyfold hU Ψ₂ Ψ₁)
        (fun x : S.TTrM hU Ψ₁ Ψ₂ => toTTrM (hU := hU) (GroupoidStr.TransitionSet.inv x))
        (fun x : S.TTrM hU Ψ₂ Ψ₁ => toTTrM (hU := hU) (GroupoidStr.TransitionSet.inv x))
        univ univ ∧
      Ψ₁.1.P.tangentPolyfold.IsScSmoothMap (S.tangentTrPolyfold hU Ψ₁ Ψ₁)
        (fun k => toTTrM (hU := hU) (GroupoidStr.TransitionSet.unit k)) ∧
      MPolyfold.IsScSmoothOnFibredProduct (S.tangentTrPolyfold hU Ψ₂ Ψ₃)
        (S.tangentTrPolyfold hU Ψ₁ Ψ₂) (S.tangentTrPolyfold hU Ψ₁ Ψ₃)
        tangentTr_isLocalScDiffeo_src tangentTr_isLocalScDiffeo_tgt.isScSmoothMap
        (fun p => toTTrM (hU := hU) (GroupoidStr.TransitionSet.mul p)) :=
  ⟨fun T => ⟨tangentTrChartExt_eq T, isScDiffeoOn_tangentTrChartExt T⟩,
    tangentTr_isLocalScDiffeo_src, tangentTr_isLocalScDiffeo_tgt, tangentTr_isScDiffeoOn_inv,
    tangentTr_isScSmoothMap_unit Ψ₁, tangentTr_isScSmoothMap_mul⟩

end GCT.PolyfoldConstruction

end Polyfold
