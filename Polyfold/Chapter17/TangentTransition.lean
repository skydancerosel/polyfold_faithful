import Polyfold.Chapter17.TangentCategory

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.2 (pp. 774–777): the transition sets `M(TΨ₁, TΨ₂)`, the maps (17.41), (17.42),
**Lemma 17.2.11**, **Proposition 17.2.12**, **Definition 17.2.13** and the source and target part
of **Proposition 17.2.14**.  Numbers and pages are the 2021 text's.

# The transition sets `M(TΨ₁, TΨ₂)` and their natural charts

## The text, paraphrased

(pp. 774–775) For `Ψ₁ ∈ F(α)`, `Ψ₂ ∈ F(α')` the transition set `M(TΨ₁, TΨ₂)` is well defined.
For `(o, φ, o') ∈ M(Ψ₁, Ψ₂)` choose an admissible triple `(U(o), U(o, φ, o'), U(o'))`;
`(s|U(o, φ, o'))⁻¹(q) = (q, φ_q, σ(q))`.  This lifts to (17.41): `T φ_q` maps `TΨ₁(k)` to
`TΨ₂(Tσ(k))` for `k ∈ T_qU(o)`, so `Φ_k = (TΨ₁(k), φ_{τ(k)}, TΨ₂(Tσ(k)))` is a morphism of `TC`
and (17.42) `TU(o) → M(TΨ₁, TΨ₂)`, `k ↦ (k, Φ_k, Tσ(k))`.  (**Lemma 17.2.11**) (1) The map can be
built for every `(o, φ, o')`; every element of `M(TΨ₁, TΨ₂)` is in the image of such a map with
`(o, φ, o')` on level `≥ 1`.  (2) If the images of two such maps intersect, the transition map is
`k ↦ k`: the data near `q₀ = τ(k₀)` coincide.  (**Proposition 17.2.12**, p. 776) There is a unique
topology on `M(TΨ₁, TΨ₂)` making the maps (17.42) homeomorphisms onto open sets; (**Definition
17.2.13**) it is the natural topology.  (**Proposition 17.2.14**, pp. 776–777) It is metrizable,
`s` and `t` are local homeomorphisms, `ι` is a homeomorphism, `u` and `m` are continuous.

## What is formalized (namespace `Polyfold.GCT.PolyfoldConstruction`)

* `injective_tangentUnifObj` (`TΨ` is injective on objects).
* `TTr hU Ψ₁ Ψ₂` (**`M(TΨ₁, TΨ₂)`**, the transition set of Definition 17.1.5 for `TΨ₁, TΨ₂`).
* `chartMor` (`Φ_k`), `chartMor_tgt` (**(17.41)**: `t(Φ_k) = TΨ₂(Tσ(k))`), `tangentTrChart`
  (**(17.42)**), `tangentTrChart_tgt` (its last entry is `Tσ(k)`).
* **`lemma_17_2_11_one`**, **`lemma_17_2_11_two`**, `lemma_17_2_11`.
* `chartTopology` (the final topology of a family of maps, namespace `Polyfold`),
  `isOpenEmbedding_chartTopology`, `eq_chartTopology`.
* `TTrIndex`, `injective_tangentTrChart`, `isOpen_tangentTrChart_preimage_image`,
  `tangentTrTopology` (**Definition 17.2.13**), **`proposition_17_2_12`**.
* `isOpenEmbedding_tangentSigma` (`Tσ` is an open embedding),
  `isLocalHomeomorph_of_comp_tangentTrChart`,
  **`proposition_17_2_14_src_tgt`** (the source and target part of Proposition 17.2.14).

## Readings

* `TU(o)` is `p⁻¹(U(o))`, the tangent vectors over the level-`1` points of `U(o)`; the map
  (17.42) is defined on it for every admissible triple of every `(o, φ, o')`, without regularity.
* (2) is read as: equal values `(k₀, Φ_{k₀}, ·)` of two maps force `k ↦ k` as transition map, and
  the two maps agree on `p⁻¹(W)` for an open neighbourhood `W` of `τ(k₀)` ("the data near `q₀`
  coincide").
* The topology of Proposition 17.2.12 is read as the final topology of the maps (17.42), one for
  every `(o, φ, o')` and every admissible triple of it; the basis `B` of the proof gives the same
  open sets.
* Only the source and target part of Proposition 17.2.14 is formalized here; metrizability and
  the continuity of `ι`, `u`, `m` are not.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

/-! ### The final topology of a family of charts -/

section ChartTopology

variable {X : Type*} {ι : Type*} {U : ι → Type*} [∀ i, TopologicalSpace (U i)]
  (φ : ∀ i, U i → X)

/-- The final topology of a family of maps `φ_i : U_i → X`: `V` is open iff every `φ_i⁻¹(V)` is
open. -/
@[instance_reducible] def chartTopology : TopologicalSpace X :=
  ⨆ i, TopologicalSpace.coinduced (φ i) inferInstance

theorem isOpen_chartTopology_iff {V : Set X} :
    IsOpen[chartTopology φ] V ↔ ∀ i, IsOpen (φ i ⁻¹' V) := by
  simp only [isOpen_iSup_iff, isOpen_coinduced]

/-- **Charts glue to a topology**: if the `φ_i` are injective and `φ_i⁻¹(φ_j(W))` is open for
every open `W` (open overlaps, continuous transitions), each `φ_i` is an open embedding for
`chartTopology φ`. -/
theorem isOpenEmbedding_chartTopology (hinj : ∀ i, Injective (φ i))
    (hcompat : ∀ i j (W : Set (U j)), IsOpen W → IsOpen (φ i ⁻¹' (φ j '' W))) (i : ι) :
    @IsOpenEmbedding _ _ _ (chartTopology φ) (φ i) := by
  let := chartTopology φ
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ (hinj i) ?_
  · exact continuous_def.2 fun V hV => (isOpen_chartTopology_iff φ).1 hV i
  · intro W hW
    exact (isOpen_chartTopology_iff φ).2 fun j => hcompat j i W hW

/-- **Uniqueness**: a topology for which the `φ_i` (covering `X`) are open embeddings is
`chartTopology φ`. -/
theorem eq_chartTopology (hcover : ∀ x, ∃ i u, φ i u = x) (t : TopologicalSpace X)
    (ht : ∀ i, @IsOpenEmbedding _ _ _ t (φ i)) : t = chartTopology φ := by
  refine TopologicalSpace.ext (funext fun V => propext ?_)
  rw [isOpen_chartTopology_iff]
  refine ⟨fun hV i => (ht i).continuous.isOpen_preimage V hV, fun hV => ?_⟩
  have hV' : V = ⋃ i, φ i '' (φ i ⁻¹' V) := by
    ext x
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · obtain ⟨i, u, rfl⟩ := hcover x
      exact mem_iUnion.2 ⟨i, u, hx, rfl⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.1 hx
      obtain ⟨u, hu, rfl⟩ := hi
      exact hu
  rw [hV']
  exact @isOpen_iUnion _ _ t _ fun i => (ht i).isOpenMap _ (hV i)

end ChartTopology

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} {S : C.PolyfoldConstruction}

/-- **`TΨ : TO → TC` is injective**: `Ψ` is injective on objects and the maps `Tσ` are
bijective on fibres. -/
theorem injective_tangentUnifObj (hU : S.HasUniformizers) (Ψ : S.Unif) :
    Injective (S.tangentUnifObj hU Ψ) := by
  intro k k' h
  have hb : basePt Ψ k = basePt Ψ k' := Ψ.1.injective_obj (congrArg TangentCatObj.base h)
  have hv := TangentCatObj.transMap_vec_of_eq h
  have hA : Ψ.1.obj (basePt Ψ k') = Ψ.1.obj (basePt Ψ k) := congrArg Ψ.1.obj hb.symm
  have h₂ : C.toGroupoidStr.comp (C.toGroupoidStr.comp
      (C.toGroupoidStr.unit (Ψ.1.obj (basePt Ψ k'))) (C.toGroupoidStr.unit (Ψ.1.obj (basePt Ψ k'))))
      (C.toGroupoidStr.unit (Ψ.1.obj (basePt Ψ k))) =
      C.toGroupoidStr.unit (Ψ.1.obj (basePt Ψ k)) := by
    rw [hA, GroupoidStr.unit_comp_of_eq (C.toGroupoidStr.tgt_unit _),
      GroupoidStr.unit_comp_of_eq (C.toGroupoidStr.tgt_unit _)]
  have h₂' : C.toGroupoidStr.comp (C.toGroupoidStr.unit (Ψ.1.obj (basePt Ψ k')))
      (C.toGroupoidStr.unit (Ψ.1.obj (basePt Ψ k'))) =
      C.toGroupoidStr.unit (Ψ.1.obj (basePt Ψ k')) :=
    GroupoidStr.unit_comp_of_eq (C.toGroupoidStr.tgt_unit _)
  set a := S.unitTr (S.refQ (tangentObj_of_unif hU Ψ k')) (basePt Ψ k') (obj_refPoint _) rfl
  calc k = S.transMap a (S.transMap (S.refUnitTr (tangentObj_of_unif hU Ψ k)
          (tangentObj_of_unif hU Ψ k') (congrArg TangentCatObj.base h))
          (S.transMap (S.unitTr (basePt Ψ k) (S.refQ (tangentObj_of_unif hU Ψ k)) rfl
            (obj_refPoint _)) k)) :=
        (transMap_three_eq_self a (S.refUnitTr (tangentObj_of_unif hU Ψ k)
          (tangentObj_of_unif hU Ψ k') (congrArg TangentCatObj.base h))
          (S.unitTr (basePt Ψ k) (S.refQ (tangentObj_of_unif hU Ψ k)) rfl (obj_refPoint _))
          rfl rfl h₂ hb.symm rfl).symm
    _ = S.transMap a (S.transMap (S.unitTr (basePt Ψ k') (S.refQ (tangentObj_of_unif hU Ψ k'))
          rfl (obj_refPoint _)) k') := congrArg (S.transMap a) hv
    _ = k' := transMap_transMap_eq_self a (S.unitTr (basePt Ψ k')
          (S.refQ (tangentObj_of_unif hU Ψ k')) rfl (obj_refPoint _)) rfl h₂' rfl rfl

variable (S) in
/-- **`M(TΨ₁, TΨ₂)`** (2021 p. 774): the transition set (Definition 17.1.5) of the tangent
uniformizers `TΨ₁ : TO₁ → TC`, `TΨ₂ : TO₂ → TC`. -/
abbrev TTr (hU : S.HasUniformizers) (Ψ₁ Ψ₂ : S.Unif) : Type (max u 1) :=
  GroupoidStr.TransitionSet S.tangentCatGroupoid (S.tangentUnifObj hU Ψ₁) (S.tangentUnifObj hU Ψ₂)

section Chart

variable {Ψ₁ Ψ₂ : S.Unif} {o : S.Tr Ψ₁ Ψ₂}

variable (S) in
/-- **`Φ_k = (TΨ₁(k), φ_{τ(k)}, ·)`** (2021 p. 775), `(s|U(o, φ, o'))⁻¹(q) = (q, φ_q, σ(q))`. -/
def chartMor (hU : S.HasUniformizers) (T : S.AdmissibleTriple o) (k : Ψ₁.1.P.TangentSpace)
    (hk : basePt Ψ₁ k ∈ T.srcSet) : S.TangentCatMor :=
  ⟨S.tangentUnifObj hU Ψ₁ k, (T.srcInv (basePt Ψ₁ k)).mor,
    (T.srcInv (basePt Ψ₁ k)).src_mor.trans (congrArg Ψ₁.1.obj (T.src_srcInv hk)),
    ⟨(tangentObj_of_unif hU Ψ₁ k).1.of_isomorphic ⟨_,
      (T.srcInv (basePt Ψ₁ k)).src_mor.trans (congrArg Ψ₁.1.obj (T.src_srcInv hk)), rfl⟩, hU _⟩⟩

/-- **(17.41)**: `T φ_q (TΨ₁(k)) = TΨ₂(Tσ(k))`, the target of `Φ_k`. -/
theorem chartMor_tgt (hU : S.HasUniformizers) (T : S.AdmissibleTriple o)
    (k : Ψ₁.1.P.TangentSpace) (hk : basePt Ψ₁ k ∈ T.srcSet) :
    (S.chartMor hU T k hk).tgt =
      S.tangentUnifObj hU Ψ₂ (S.transMap (T.srcInv (basePt Ψ₁ k)) k) := by
  set b := T.srcInv (basePt Ψ₁ k)
  have hbs : b.src = basePt Ψ₁ k := T.src_srcInv hk
  have hq : basePt Ψ₂ (S.transMap b k) = b.tgt := base_transMap b hbs.symm
  have hb : C.toGroupoidStr.tgt b.mor = Ψ₂.1.obj (basePt Ψ₂ (S.transMap b k)) :=
    b.tgt_mor.trans (congrArg Ψ₂.1.obj hq.symm)
  refine TangentCatObj.ext_of hb ?_
  have h₂ : C.toGroupoidStr.comp (C.toGroupoidStr.comp
      (C.toGroupoidStr.unit (Ψ₂.1.obj (basePt Ψ₂ (S.transMap b k)))) b.mor)
      (C.toGroupoidStr.unit (Ψ₁.1.obj (basePt Ψ₁ k))) =
      C.toGroupoidStr.comp (C.toGroupoidStr.unit (Ψ₂.1.obj (basePt Ψ₂ (S.transMap b k)))) b.mor :=
    GroupoidStr.comp_unit_of_eq ((C.toGroupoidStr.src_comp _ _
      ((C.toGroupoidStr.src_unit _).trans hb.symm)).trans (S.chartMor hU T k hk).src_eq)
  exact transMap_three_eq
    (S.refUnitTr (S.chartMor hU T k hk).isObj_tgt (tangentObj_of_unif hU Ψ₂ _) hb)
    (S.refTr (tangentObj_of_unif hU Ψ₁ k) (S.chartMor hU T k hk).isObj_tgt b.mor
      (S.chartMor hU T k hk).src_eq rfl)
    (S.unitTr (basePt Ψ₁ k) (S.refQ (tangentObj_of_unif hU Ψ₁ k)) rfl (obj_refPoint _))
    (S.unitTr (basePt Ψ₂ (S.transMap b k)) (S.refQ (tangentObj_of_unif hU Ψ₂ _)) rfl
      (obj_refPoint _))
    b rfl rfl hq hbs.symm h₂ rfl rfl

variable (S) in
/-- **The map (17.42)** `TU(o) → M(TΨ₁, TΨ₂)`, `k ↦ (k, Φ_k, Tσ(k))` (2021 p. 775), on
`TU(o) = p⁻¹(U(o))`, for an admissible triple of `(o, φ, o')`. -/
def tangentTrChart (hU : S.HasUniformizers) (T : S.AdmissibleTriple o)
    (k : Ψ₁.1.P.tangentPreimage T.srcSet) : S.TTr hU Ψ₁ Ψ₂ :=
  ⟨k.1, S.chartMor hU T k.1 k.2, S.transMap (T.srcInv (basePt Ψ₁ k.1)) k.1, rfl,
    chartMor_tgt hU T k.1 k.2⟩

theorem tangentTrChart_src (hU : S.HasUniformizers) (T : S.AdmissibleTriple o)
    (k : Ψ₁.1.P.tangentPreimage T.srcSet) : (S.tangentTrChart hU T k).src = k.1 := rfl

/-- The last entry of `(k, Φ_k, Tσ(k))` is `Tσ(k)`, the tangent of `σ : U(o) → U(o')`. -/
theorem tangentTrChart_tgt (hU : S.HasUniformizers) (T : S.AdmissibleTriple o)
    (k : Ψ₁.1.P.tangentPreimage T.srcSet) :
    (S.tangentTrChart hU T k).tgt = MPolyfold.tangentMapOn T.isScSmoothOn_sigma k.1 :=
  transMap_eq_of_mem T (T.srcInv_mem k.2) (T.src_srcInv k.2).symm

/-- The morphism of `(k, Φ_k, Tσ(k))` is over `φ_{τ(k)}`. -/
theorem tangentTrChart_mor (hU : S.HasUniformizers) (T : S.AdmissibleTriple o)
    (k : Ψ₁.1.P.tangentPreimage T.srcSet) :
    (S.tangentTrChart hU T k).mor.mor = (T.srcInv (basePt Ψ₁ k.1)).mor := rfl

end Chart

/-- **Lemma 17.2.11 (1)** (2021 p. 775): every element `(k, Φ, k')` of `M(TΨ₁, TΨ₂)` is the image
of `k` under the map (17.42) of an admissible triple of `(τ(k), P(Φ), τ(k')) ∈ M(Ψ₁, Ψ₂)`, which
lies on level `≥ 1`.  (The map exists for every `(o, φ, o')`: `tangentTrChart`.) -/
theorem lemma_17_2_11_one (hU : S.HasUniformizers) {Ψ₁ Ψ₂ : S.Unif} (x : S.TTr hU Ψ₁ Ψ₂) :
    ∃ (o : S.Tr Ψ₁ Ψ₂) (T : S.AdmissibleTriple o) (k : Ψ₁.1.P.tangentPreimage T.srcSet),
      o.src ∈ Ψ₁.1.P.levelSet 1 ∧ S.tangentTrChart hU T k = x := by
  let o : S.Tr Ψ₁ Ψ₂ := ⟨basePt Ψ₁ x.src, x.mor.mor, basePt Ψ₂ x.tgt,
    x.mor.src_eq.trans (congrArg TangentCatObj.base x.src_mor),
    congrArg TangentCatObj.base x.tgt_mor⟩
  let T := S.triple o
  have hso : T.srcInv (basePt Ψ₁ x.src) = o := T.srcInv_eq T.mem_carrier
  refine ⟨o, T, ⟨x.src, T.src_mem⟩, MPolyfold.levelVal_mem _, ?_⟩
  have hmor : S.chartMor hU T x.src T.src_mem = x.mor :=
    TangentCatMor.ext' x.src_mor.symm (congrArg GroupoidStr.TransitionSet.mor hso)
  refine GroupoidStr.TransitionSet.ext rfl hmor ?_
  refine injective_tangentUnifObj hU Ψ₂ ?_
  exact (chartMor_tgt hU T x.src T.src_mem).symm.trans
    ((congrArg TangentCatMor.tgt hmor).trans x.tgt_mor)

/-- **Lemma 17.2.11 (2)** (2021 p. 775): if two maps (17.42) take a common value at `k₀`, the
transition map is `k ↦ k`, and the maps agree on `p⁻¹(W)` for an open neighbourhood `W` of
`τ(k₀)` (the sections `(s|U)⁻¹` of the two triples agree near `τ(k₀)`). -/
theorem lemma_17_2_11_two (hU : S.HasUniformizers) {Ψ₁ Ψ₂ : S.Unif} {o₁ o₂ : S.Tr Ψ₁ Ψ₂}
    (T₁ : S.AdmissibleTriple o₁) (T₂ : S.AdmissibleTriple o₂)
    (k₁ : Ψ₁.1.P.tangentPreimage T₁.srcSet) (k₂ : Ψ₁.1.P.tangentPreimage T₂.srcSet)
    (h : S.tangentTrChart hU T₁ k₁ = S.tangentTrChart hU T₂ k₂) :
    k₁.1 = k₂.1 ∧ ∃ W : Set Ψ₁.1.O, IsOpen W ∧ basePt Ψ₁ k₁.1 ∈ W ∧
      W ⊆ T₁.srcSet ∩ T₂.srcSet ∧
      ∀ k (hk₁ : k ∈ Ψ₁.1.P.tangentPreimage T₁.srcSet)
        (hk₂ : k ∈ Ψ₁.1.P.tangentPreimage T₂.srcSet), basePt Ψ₁ k ∈ W →
        S.tangentTrChart hU T₁ ⟨k, hk₁⟩ = S.tangentTrChart hU T₂ ⟨k, hk₂⟩ := by
  have hk : k₁.1 = k₂.1 := congrArg GroupoidStr.TransitionSet.src h
  refine ⟨hk, ?_⟩
  obtain ⟨k₀, h₁⟩ := k₁
  obtain ⟨k₀', h₂⟩ := k₂
  dsimp only at hk
  subst hk
  set q₀ := basePt Ψ₁ k₀
  have hm : (T₁.srcInv q₀).mor = (T₂.srcInv q₀).mor :=
    congrArg (fun x : S.TTr hU Ψ₁ Ψ₂ => x.mor.mor) h
  have ht : S.transMap (T₁.srcInv q₀) k₀ = S.transMap (T₂.srcInv q₀) k₀ :=
    congrArg GroupoidStr.TransitionSet.tgt h
  have hb : T₁.srcInv q₀ = T₂.srcInv q₀ :=
    GroupoidStr.TransitionSet.ext ((T₁.src_srcInv h₁).trans (T₂.src_srcInv h₂).symm) hm
      ((base_transMap _ (T₁.src_srcInv h₁).symm).symm.trans
        ((congrArg (basePt Ψ₂) ht).trans (base_transMap _ (T₂.src_srcInv h₂).symm)))
  let T₁' : S.AdmissibleTriple (T₂.srcInv q₀) :=
    ⟨T₁.srcSet, T₁.carrier, T₁.tgtSet, T₁.srcInv, T₁.tgtInv, hb ▸ T₁.srcInv_mem h₁,
      T₁.isScDiffeoOn_src, T₁.isScDiffeoOn_tgt⟩
  have hq₂ : (T₂.srcInv q₀).src = q₀ := T₂.src_srcInv h₂
  obtain ⟨W, hWo, hqW, hWsub, hWeq⟩ := T₁'.exists_srcInv_eq (f := T₂.srcInv) T₂.isOpen_srcSet
    (hq₂.symm ▸ h₂) T₂.isScDiffeoOn_src.isScSmoothOn_inv.continuousOn
    (fun p hp => T₂.src_srcInv hp) (congrArg T₂.srcInv hq₂)
  refine ⟨W, hWo, hq₂ ▸ hqW, fun p hp => ⟨(hWsub hp).2, (hWsub hp).1⟩, fun k hk₁ hk₂ hkW => ?_⟩
  have he : T₁.srcInv (basePt Ψ₁ k) = T₂.srcInv (basePt Ψ₁ k) := hWeq _ hkW
  exact GroupoidStr.TransitionSet.ext rfl (TangentCatMor.ext' rfl
    (congrArg GroupoidStr.TransitionSet.mor he))
    (congrArg (fun b => S.transMap b k) he)

/-- **Lemma 17.2.11** (2021 p. 775), both parts. -/
theorem lemma_17_2_11 (hU : S.HasUniformizers) (Ψ₁ Ψ₂ : S.Unif) :
    (∀ x : S.TTr hU Ψ₁ Ψ₂, ∃ (o : S.Tr Ψ₁ Ψ₂) (T : S.AdmissibleTriple o)
      (k : Ψ₁.1.P.tangentPreimage T.srcSet),
        o.src ∈ Ψ₁.1.P.levelSet 1 ∧ S.tangentTrChart hU T k = x) ∧
    ∀ {o₁ o₂ : S.Tr Ψ₁ Ψ₂} (T₁ : S.AdmissibleTriple o₁) (T₂ : S.AdmissibleTriple o₂)
      (k₁ : Ψ₁.1.P.tangentPreimage T₁.srcSet) (k₂ : Ψ₁.1.P.tangentPreimage T₂.srcSet),
      S.tangentTrChart hU T₁ k₁ = S.tangentTrChart hU T₂ k₂ →
        k₁.1 = k₂.1 ∧ ∃ W : Set Ψ₁.1.O, IsOpen W ∧ basePt Ψ₁ k₁.1 ∈ W ∧
          W ⊆ T₁.srcSet ∩ T₂.srcSet ∧
          ∀ k (hk₁ : k ∈ Ψ₁.1.P.tangentPreimage T₁.srcSet)
            (hk₂ : k ∈ Ψ₁.1.P.tangentPreimage T₂.srcSet), basePt Ψ₁ k ∈ W →
            S.tangentTrChart hU T₁ ⟨k, hk₁⟩ = S.tangentTrChart hU T₂ ⟨k, hk₂⟩ :=
  ⟨lemma_17_2_11_one hU, fun T₁ T₂ k₁ k₂ h => lemma_17_2_11_two hU T₁ T₂ k₁ k₂ h⟩

/-! ### Proposition 17.2.12, Definition 17.2.13 -/

variable (S) in
/-- The index set of the maps (17.42): the admissible triples of the elements of `M(Ψ₁, Ψ₂)`. -/
abbrev TTrIndex (Ψ₁ Ψ₂ : S.Unif) : Type u := Σ o : S.Tr Ψ₁ Ψ₂, S.AdmissibleTriple o

theorem injective_tangentTrChart (hU : S.HasUniformizers) {Ψ₁ Ψ₂ : S.Unif} {o : S.Tr Ψ₁ Ψ₂}
    (T : S.AdmissibleTriple o) : Injective (S.tangentTrChart hU T) := fun _ _ h =>
  Subtype.ext (congrArg GroupoidStr.TransitionSet.src h)

/-- The overlaps of two maps (17.42) are open and the transitions `k ↦ k` continuous
(Lemma 17.2.11 (2)). -/
theorem isOpen_tangentTrChart_preimage_image (hU : S.HasUniformizers) {Ψ₁ Ψ₂ : S.Unif}
    {o₁ o₂ : S.Tr Ψ₁ Ψ₂} (T₁ : S.AdmissibleTriple o₁) (T₂ : S.AdmissibleTriple o₂)
    (W : Set (Ψ₁.1.P.tangentPreimage T₂.srcSet)) (hW : IsOpen W) :
    IsOpen (S.tangentTrChart hU T₁ ⁻¹' (S.tangentTrChart hU T₂ '' W)) := by
  obtain ⟨W', hW'o, rfl⟩ := isOpen_induced_iff.1 hW
  refine isOpen_iff_forall_mem_open.2 fun k hk => ?_
  obtain ⟨k', hk'W, hkk'⟩ := hk
  obtain ⟨heq, N, hNo, hkN, hNsub, hagree⟩ := lemma_17_2_11_two hU T₂ T₁ k' k hkk'
  refine ⟨Subtype.val ⁻¹' (Ψ₁.1.P.tangentPreimage N ∩ W'), ?_, ?_, ?_⟩
  · rintro k₁ ⟨hk₁N, hk₁W⟩
    exact ⟨⟨k₁.1, (hNsub hk₁N).1⟩, hk₁W, hagree k₁.1 (hNsub hk₁N).1 k₁.2 hk₁N⟩
  · exact ((MPolyfold.isOpen_tangentPreimage hNo).inter hW'o).preimage continuous_subtype_val
  · exact ⟨heq ▸ hkN, heq ▸ hk'W⟩

variable (S) in
/-- **Definition 17.2.13** (2021 p. 776): **the natural topology `T` on `M(TΨ₁, TΨ₂)`**, the
final topology of the maps (17.42) (unique by Proposition 17.2.12). -/
@[instance_reducible] def tangentTrTopology (hU : S.HasUniformizers) (Ψ₁ Ψ₂ : S.Unif) :
    TopologicalSpace (S.TTr hU Ψ₁ Ψ₂) :=
  chartTopology (U := fun i : S.TTrIndex Ψ₁ Ψ₂ => Ψ₁.1.P.tangentPreimage i.2.srcSet)
    fun i => S.tangentTrChart hU i.2

/-- **Proposition 17.2.12** (2021 p. 776): there is a unique topology on `M(TΨ₁, TΨ₂)` making
the maps (17.42) homeomorphisms onto open sets: the natural topology `tangentTrTopology`. -/
theorem proposition_17_2_12 (hU : S.HasUniformizers) (Ψ₁ Ψ₂ : S.Unif) :
    (∀ {o : S.Tr Ψ₁ Ψ₂} (T : S.AdmissibleTriple o),
      @IsOpenEmbedding _ _ _ (S.tangentTrTopology hU Ψ₁ Ψ₂) (S.tangentTrChart hU T)) ∧
    ∀ t : TopologicalSpace (S.TTr hU Ψ₁ Ψ₂),
      (∀ {o : S.Tr Ψ₁ Ψ₂} (T : S.AdmissibleTriple o),
        @IsOpenEmbedding _ _ _ t (S.tangentTrChart hU T)) →
      t = S.tangentTrTopology hU Ψ₁ Ψ₂ := by
  refine ⟨fun {o} T => isOpenEmbedding_chartTopology
    (U := fun i : S.TTrIndex Ψ₁ Ψ₂ => Ψ₁.1.P.tangentPreimage i.2.srcSet)
    (fun i => S.tangentTrChart hU i.2) (fun i => injective_tangentTrChart hU i.2)
    (fun i j W hW => isOpen_tangentTrChart_preimage_image hU i.2 j.2 W hW) ⟨o, T⟩,
    fun t ht => eq_chartTopology
      (U := fun i : S.TTrIndex Ψ₁ Ψ₂ => Ψ₁.1.P.tangentPreimage i.2.srcSet)
      (fun i => S.tangentTrChart hU i.2) (fun x => ?_) t fun i => ht i.2⟩
  obtain ⟨o, T, k, -, hk⟩ := lemma_17_2_11_one hU x
  exact ⟨⟨o, T⟩, k, hk⟩

/-! ### Proposition 17.2.14: `s` and `t` are local homeomorphisms -/

/-- `Tσ : TU(o) → TO'` is an open embedding (`σ : U(o) → U(o')` an sc-diffeomorphism). -/
theorem isOpenEmbedding_tangentSigma {Ψ₁ Ψ₂ : S.Unif} {o : S.Tr Ψ₁ Ψ₂}
    (T : S.AdmissibleTriple o) :
    IsOpenEmbedding fun k : Ψ₁.1.P.tangentPreimage T.srcSet =>
      MPolyfold.tangentMapOn T.isScSmoothOn_sigma k.1 := by
  have hd := T.isScDiffeoOn_sigma
  have hU₁ : IsOpen (Ψ₁.1.P.tangentPreimage T.srcSet) :=
    MPolyfold.isOpen_tangentPreimage T.isOpen_srcSet
  have hU₂ : IsOpen (Ψ₂.1.P.tangentPreimage T.tgtSet) :=
    MPolyfold.isOpen_tangentPreimage hd.isOpen_target
  have hc₁ := MPolyfold.continuousOn_tangentMapOn hd.isScSmoothOn
  have hc₂ := MPolyfold.continuousOn_tangentMapOn hd.isScSmoothOn_inv
  have hleft : ∀ α ∈ Ψ₁.1.P.tangentPreimage T.srcSet,
      MPolyfold.tangentMapOn hd.isScSmoothOn_inv (MPolyfold.tangentMapOn hd.isScSmoothOn α) = α :=
    fun α hα => by
      have h1 := MPolyfold.tangentMapOn_comp hd.isScSmoothOn_inv hd.isScSmoothOn hd.mapsTo hα
      rw [Function.comp_apply] at h1
      rw [← h1]
      exact MPolyfold.tangentMapOn_eqOn_id _ (fun x hx => hd.left_inv x hx) hα
  have hmaps := MPolyfold.tangentMapOn_mapsTo hd.isScSmoothOn hd.mapsTo
  have hmaps' := MPolyfold.tangentMapOn_mapsTo hd.isScSmoothOn_inv hd.mapsTo_inv
  have hright : ∀ β ∈ Ψ₂.1.P.tangentPreimage T.tgtSet,
      MPolyfold.tangentMapOn hd.isScSmoothOn (MPolyfold.tangentMapOn hd.isScSmoothOn_inv β) = β :=
    fun β hβ => by
      have h1 := MPolyfold.tangentMapOn_comp hd.isScSmoothOn hd.isScSmoothOn_inv hd.mapsTo_inv hβ
      rw [Function.comp_apply] at h1
      rw [← h1]
      exact MPolyfold.tangentMapOn_eqOn_id _ (fun y hy => hd.right_inv y hy) hβ
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap
    (hc₁.comp_continuous continuous_subtype_val fun k => k.2) (fun k k' h => Subtype.ext ?_) ?_
  · exact (hleft k.1 k.2).symm.trans ((congrArg _ h).trans (hleft k'.1 k'.2))
  · intro V hV
    obtain ⟨V', hV'o, rfl⟩ := isOpen_induced_iff.1 hV
    have : (fun k : Ψ₁.1.P.tangentPreimage T.srcSet =>
        MPolyfold.tangentMapOn T.isScSmoothOn_sigma k.1) '' (Subtype.val ⁻¹' V') =
        Ψ₂.1.P.tangentPreimage T.tgtSet ∩
          MPolyfold.tangentMapOn hd.isScSmoothOn_inv ⁻¹'
            (Ψ₁.1.P.tangentPreimage T.srcSet ∩ V') := by
      ext β
      refine ⟨?_, fun hβ => ⟨⟨_, hβ.2.1⟩, hβ.2.2, hright β hβ.1⟩⟩
      rintro ⟨k, hk, rfl⟩
      exact ⟨hmaps k.2, by rw [mem_preimage, hleft k.1 k.2]; exact ⟨k.2, hk⟩⟩
    rw [this]
    exact hc₂.isOpen_inter_preimage hU₂ (hU₁.inter hV'o)

/-- A map out of `M(TΨ₁, TΨ₂)` whose composites with the maps (17.42) are open embeddings is a
local homeomorphism for the natural topology. -/
theorem isLocalHomeomorph_of_comp_tangentTrChart (hU : S.HasUniformizers) {Ψ₁ Ψ₂ : S.Unif}
    {Y : Type*} [TopologicalSpace Y] (g : S.TTr hU Ψ₁ Ψ₂ → Y)
    (hg : ∀ {o : S.Tr Ψ₁ Ψ₂} (T : S.AdmissibleTriple o),
      IsOpenEmbedding (g ∘ S.tangentTrChart hU T)) :
    @IsLocalHomeomorph _ _ (S.tangentTrTopology hU Ψ₁ Ψ₂) _ g := by
  let := S.tangentTrTopology hU Ψ₁ Ψ₂
  refine isLocalHomeomorph_iff_isOpenEmbedding_restrict.2 fun x => ?_
  obtain ⟨o, T, k, -, rfl⟩ := lemma_17_2_11_one hU x
  have he := (proposition_17_2_12 hU Ψ₁ Ψ₂).1 T
  refine ⟨range (S.tangentTrChart hU T), he.isOpen_range.mem_nhds ⟨k, rfl⟩, ?_⟩
  set e := he.isEmbedding.toHomeomorph
  have hfun : (range (S.tangentTrChart hU T)).domRestrict g =
      (g ∘ S.tangentTrChart hU T) ∘ e.symm := by
    funext y
    obtain ⟨_, k', rfl⟩ := y
    change g _ = g (S.tangentTrChart hU T (e.symm (e k')))
    rw [e.symm_apply_apply]
  rw [hfun]
  exact (hg T).comp e.symm.isOpenEmbedding

/-- **Proposition 17.2.14, `s` and `t`** (2021 p. 776): for the natural topology,
`s, t : M(TΨ₁, TΨ₂) → TO₁, TO₂` are local homeomorphisms: on the image of a map (17.42), `s` is
the inverse of the map and `t` is `Tσ` composed with it. -/
theorem proposition_17_2_14_src_tgt (hU : S.HasUniformizers) (Ψ₁ Ψ₂ : S.Unif) :
    @IsLocalHomeomorph _ _ (S.tangentTrTopology hU Ψ₁ Ψ₂) _
        (fun x : S.TTr hU Ψ₁ Ψ₂ => x.src) ∧
      @IsLocalHomeomorph _ _ (S.tangentTrTopology hU Ψ₁ Ψ₂) _
        (fun x : S.TTr hU Ψ₁ Ψ₂ => x.tgt) := by
  refine ⟨isLocalHomeomorph_of_comp_tangentTrChart hU _ fun T => ?_,
    isLocalHomeomorph_of_comp_tangentTrChart hU _ fun T => ?_⟩
  · exact (MPolyfold.isOpen_tangentPreimage T.isOpen_srcSet).isOpenEmbedding_subtypeVal
  · have h : ((fun x : S.TTr hU Ψ₁ Ψ₂ => x.tgt) ∘ S.tangentTrChart hU T) =
        fun k => MPolyfold.tangentMapOn T.isScSmoothOn_sigma k.1 :=
      funext fun k => tangentTrChart_tgt hU T k
    rw [h]
    exact isOpenEmbedding_tangentSigma T

end GCT.PolyfoldConstruction

end Polyfold
