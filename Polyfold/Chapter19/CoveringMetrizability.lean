import Polyfold.Chapter19.CoveringLocalStructure
import Polyfold.Chapter17.ProperCoveringStructure

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 19, §19.7
"Covering Constructions", pp. 922–926: **Remark 19.7.22** (p. 923), **Proposition 19.7.23**
(p. 923), **Proposition 19.7.24** (p. 924) and **Theorem 19.7.25 (1)–(4a)** (pp. 925–926).
Numbers and pages are the 2021 text's.

# Properness, paracompactness and metrizability of `|A|`

## The text, paraphrased

(Remark 19.7.22) By Proposition 19.4.7 the metrizability of `T_{|B|}` is equivalent to the
properness condition with paracompactness; Lemma 19.7.21 (2) holds if `T_{|B|}` is metrizable.
(Proposition 19.7.23) `T_{|A|}` satisfies the properness condition if and only if `T_{|B|}` does.
(Proposition 19.7.24) `T_{|A|}` is paracompact if and only if `T_{|B|}` is.  Both proofs use
Corollary 19.7.20.  (Theorem 19.7.25) If `T_{|B|}` is metrizable: (1) `T_{|A|}` is metrizable and
`|P|` is a surjective continuous map; (2) `A` and `B` with their natural topologies are GCTs;
(3) `P` is a proper covering functor of GCTs (Definition 17.8.1); (4) for every `z ∈ |B|` the
preimage is finite, `{z̄₁, …, z̄ₖ}`, and there are open neighbourhoods `U(z)`, `U(z̄ᵢ)` with (a) the
`U(z̄ᵢ)` mutually disjoint and `|P|⁻¹(U(z)) = ⊔ U(z̄ᵢ)`; (b) `|P| : U(z̄ᵢ) → U(z)` a
homeomorphism.

## What is formalized

Point-set lemmas (`Polyfold.Chapter19`), for `f : X → Y` continuous with finite fibres such that
every open `U ⊇ f⁻¹(y)` contains some `f⁻¹(V)`, `V ∋ y` open (a perfect map):
`paracompactSpace_of_tube` (`Y` paracompact ⇒ `X` paracompact),
`paracompactSpace_of_tube_of_isOpenMap` (`X` paracompact, `f` open and surjective ⇒ `Y`
paracompact), `t2Space_of_disjoint_fibre_nhds`.

Under `IsCompatible` (an added hypothesis, the reading of l. 44572; hence the `_hyp` suffixes) and
`HasClassUniformizers` (`F(α) ≠ ∅`, the standing reading of §17.1), the hypotheses of `natTopA`:
* **Remark 19.7.22**: `remark_19_7_22`.
* `PropernessV2A`: the properness condition (Definition 19.4.1 (2)) for `T_{|A|}`, read through
  the uniformizers `Ψ̂ : E → A` of `F̂`.  **Proposition 19.7.23**: `proposition_19_7_23_hyp`.
* **Proposition 19.7.24**: `proposition_19_7_24_hyp`.
* `t2Space_natTopA`, `exists_metrizable_nhds_natTopA` (`T_{|A|}` is locally metrizable, Lemma
  19.7.17 and Theorem 7.3.1).
* **Theorem 19.7.25**: `theorem_19_7_25_one_hyp` (through Smirnov's theorem
  `metrizableSpace_of_locally`, i.e. `metrizableSpace_of_pullback` along `id`), the GCTs
  `toGCTA`, `toGCTB` with `theorem_19_7_25_two_hyp`, `theorem_19_7_25_three_hyp` (Definition 17.8.1
  for `P : toGCTA → toGCTB`), `theorem_19_7_25_four_a_hyp`.  (4b) does not hold as we read it
  (`not_theorem_19_7_25_four_b`, Chapter 19's `CoveringCounterexamples.lean`).

## Readings

* The proofs of Propositions 19.7.23 and 19.7.24 use Corollary 19.7.20, including its part (3),
  which does not hold as we read it.  What they need is that `|P|` is continuous, open,
  surjective, with finite fibres, and that every open neighbourhood of `|P|⁻¹(z)` contains some
  `|P|⁻¹(W(z))` (Corollary 19.7.20 (2), `exists_isOpen_preimage_subset`), i.e. that `|P|` is a
  perfect map (`isClosedMap_orbitMap`); the statements hold as printed.
* "`T_{|A|}` satisfies the properness condition" (Proposition 19.7.23): `A` has no
  translation-groupoid uniformizers; we read Definition 19.4.1 (2) with the uniformizers
  `Ψ̂ : E → A` of `F̂` and `|Ψ̂(E)|` in place of `|Ψ(O)|`: every `e ∈ E` has an open `U(e)` with
  `cl_{|A|}(|Ψ̂(U(e))|) ⊂ |Ψ̂(E)|` (`PropernessV2A`); for `T_{|B|}` it is Definition 19.4.1 (2)
  (`PropernessV2`, the form used in Lemma 19.7.21).
* Theorem 19.7.25 (1): the metrizability of `T_{|A|}` from paracompactness (Proposition 19.7.24),
  Hausdorffness (the disjoint neighbourhoods of Corollary 19.7.20 (2)) and local metrizability.
  (2): `A`, `B` with `T_{|A|}`, `T_{|B|}` as GCTs (Definition 17.1.1: a metrizable topology on the
  orbit space).
-/

open Set Function Topology TopologicalSpace

noncomputable section

namespace Polyfold

universe u

/-! ### Perfect maps -/

namespace Chapter19

section Perfect

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/-- **The preimage of a paracompact space under a perfect map is paracompact**: for `f`
continuous with finite fibres such that every open `U ⊇ f⁻¹(y)` contains some `f⁻¹(V)`, `V ∋ y`
open (the first half of the proof of Proposition 19.7.24). -/
theorem paracompactSpace_of_tube [ParacompactSpace Y] (hc : Continuous f)
    (hfin : ∀ y, (f ⁻¹' {y}).Finite)
    (htube : ∀ (y : Y) (U : Set X), IsOpen U → f ⁻¹' {y} ⊆ U →
      ∃ V, IsOpen V ∧ y ∈ V ∧ f ⁻¹' V ⊆ U) :
    ParacompactSpace X := by
  refine ⟨fun α s hso hsU => ?_⟩
  have hcov : ∀ x, ∃ a, x ∈ s a := fun x => mem_iUnion.1 (hsU.symm ▸ mem_univ x)
  choose a ha using hcov
  have hT : ∀ y, ∃ V, IsOpen V ∧ y ∈ V ∧ f ⁻¹' V ⊆ ⋃ x ∈ f ⁻¹' {y}, s (a x) := fun y =>
    htube y _ (isOpen_biUnion fun x _ => hso (a x)) fun x hx => mem_iUnion₂.2 ⟨x, hx, ha x⟩
  choose V hVo hyV hVsub using hT
  obtain ⟨β, t, hto, htU, htlf, htsub⟩ := ParacompactSpace.locallyFinite_refinement
    Y V hVo (eq_univ_of_forall fun y => mem_iUnion.2 ⟨y, hyV y⟩)
  choose yb hyb using htsub
  let T : β × X → Set X := fun p => f ⁻¹' t p.1 ∩ s (a p.2) ∩ {_w | f p.2 = yb p.1}
  refine ⟨β × X, T, fun p => ?_, ?_, ?_, fun p => ⟨a p.2, fun w hw => hw.1.2⟩⟩
  · by_cases h : f p.2 = yb p.1
    · have he : {_w : X | f p.2 = yb p.1} = univ := eq_univ_of_forall fun _ => h
      simp only [T, he, inter_univ]
      exact ((hto p.1).preimage hc).inter (hso _)
    · have he : {_w : X | f p.2 = yb p.1} = ∅ := eq_empty_of_forall_notMem fun _ hw => h hw
      simp only [T, he, inter_empty]
      exact isOpen_empty
  · refine eq_univ_of_forall fun w => ?_
    obtain ⟨b, hb⟩ := mem_iUnion.1 (htU.symm ▸ mem_univ (f w))
    obtain ⟨x, hx, hwx⟩ := mem_iUnion₂.1 (hVsub (yb b) (hyb b hb))
    exact mem_iUnion.2 ⟨(b, x), ⟨hb, hwx⟩, hx⟩
  · intro w
    obtain ⟨N, hN, hNfin⟩ := htlf (f w)
    refine ⟨f ⁻¹' N, hc.continuousAt.preimage_mem_nhds hN, ?_⟩
    refine (hNfin.biUnion fun b _ => (hfin (yb b)).image fun x => (b, x)).subset ?_
    rintro ⟨b, x⟩ ⟨w', ⟨⟨hw't, -⟩, hx⟩, hw'N⟩
    exact mem_iUnion₂.2 ⟨b, ⟨f w', hw't, hw'N⟩, x, hx, rfl⟩

/-- **The image of a paracompact space under an open perfect surjection is paracompact** (the
second half of the proof of Proposition 19.7.24). -/
theorem paracompactSpace_of_tube_of_isOpenMap [ParacompactSpace X] (hc : Continuous f)
    (hs : Surjective f) (ho : IsOpenMap f) (hfin : ∀ y, (f ⁻¹' {y}).Finite)
    (htube : ∀ (y : Y) (U : Set X), IsOpen U → f ⁻¹' {y} ⊆ U →
      ∃ V, IsOpen V ∧ y ∈ V ∧ f ⁻¹' V ⊆ U) :
    ParacompactSpace Y := by
  refine ⟨fun α s hso hsU => ?_⟩
  obtain ⟨β, t, hto, htU, htlf, htsub⟩ := ParacompactSpace.locallyFinite_refinement α
    (fun a => f ⁻¹' s a) (fun a => (hso a).preimage hc) (by rw [← preimage_iUnion, hsU,
      preimage_univ])
  refine ⟨β, fun b => f '' t b, fun b => ho _ (hto b), ?_, ?_, fun b => ?_⟩
  · rw [← image_iUnion, htU, image_univ, hs.range_eq]
  · intro y
    have hN : ∀ x, ∃ N, IsOpen N ∧ x ∈ N ∧ {b | (t b ∩ N).Nonempty}.Finite := fun x => by
      obtain ⟨N, hN, hfinN⟩ := htlf x
      obtain ⟨N', hN'N, hN'o, hxN'⟩ := mem_nhds_iff.1 hN
      exact ⟨N', hN'o, hxN', hfinN.subset fun b ⟨w, hw, hwN⟩ => ⟨w, hw, hN'N hwN⟩⟩
    choose N hNo hxN hNfin using hN
    obtain ⟨V, hVo, hyV, hVsub⟩ := htube y (⋃ x ∈ f ⁻¹' {y}, N x)
      (isOpen_biUnion fun x _ => hNo x) fun x hx => mem_iUnion₂.2 ⟨x, hx, hxN x⟩
    refine ⟨V, hVo.mem_nhds hyV, ((hfin y).biUnion fun x _ => hNfin x).subset ?_⟩
    rintro b ⟨_, ⟨w, hw, rfl⟩, hwV⟩
    obtain ⟨x, hx, hwx⟩ := mem_iUnion₂.1 (hVsub hwV)
    exact mem_iUnion₂.2 ⟨x, hx, w, hw, hwx⟩
  · obtain ⟨a, ha⟩ := htsub b
    exact ⟨a, (image_mono ha).trans (image_preimage_subset f _)⟩

/-- **Hausdorffness from disjoint neighbourhoods of the fibres**: `f` continuous into a Hausdorff
space, the points of every fibre having mutually disjoint open neighbourhoods. -/
theorem t2Space_of_disjoint_fibre_nhds [T2Space Y] (hc : Continuous f)
    (h : ∀ y, ∃ V : X → Set X, (∀ x ∈ f ⁻¹' {y}, IsOpen (V x) ∧ x ∈ V x) ∧
      (f ⁻¹' {y}).PairwiseDisjoint V) : T2Space X := by
  refine ⟨fun x x' hne => ?_⟩
  by_cases hf : f x = f x'
  · obtain ⟨V, hV, hd⟩ := h (f x)
    have hx : x ∈ f ⁻¹' {f x} := rfl
    have hx' : x' ∈ f ⁻¹' {f x} := hf.symm
    exact ⟨V x, V x', (hV x hx).1, (hV x' hx').1, (hV x hx).2, (hV x' hx').2, hd hx hx' hne⟩
  · obtain ⟨u, v, hu, hv, hxu, hyv, huv⟩ := t2_separation hf
    exact ⟨f ⁻¹' u, f ⁻¹' v, hu.preimage hc, hv.preimage hc, hxu, hyv, huv.preimage f⟩

end Perfect

end Chapter19

namespace GroupoidalCategory

variable {A B : GroupoidalCategory.{u}} {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr}

namespace CoveringBasicConstruction

variable (Bh : CoveringBasicConstruction P)

/-! ### Remark 19.7.22 -/

/-- **2021 Remark 19.7.22, p. 923**, under `HasClassUniformizers`: `T_{|B|}` is metrizable if and
only if `(F, 𝓕)` satisfies the properness condition and `T_{|B|}` is paracompact (Proposition
19.4.7), and then every `M(Ψ, Ψ')` and `M(Ψ̂, Ψ̂')` is metrizable (Lemma 19.7.21 (2)). -/
theorem remark_19_7_22 (hP : IsFiniteToOneCovering P) (hU : Bh.HasClassUniformizers) :
    (@MetrizableSpace _ (Bh.toBasic.natTop hU.toBasic) ↔
      Bh.toBasic.PropernessV2 hU.toBasic ∧ @ParacompactSpace _ (Bh.toBasic.natTop hU.toBasic)) ∧
    (@MetrizableSpace _ (Bh.toBasic.natTop hU.toBasic) →
      ∀ x y : Bh.hatU.Unif, MetrizableSpace (Bh.MB x y) ∧ MetrizableSpace (Bh.MHat x y)) :=
  ⟨Bh.toBasic.proposition_19_4_7 hU.toBasic, fun _ => (Bh.lemma_19_7_21 hP hU).2.1⟩

/-! ### Proposition 19.7.23 -/

/-- **The properness condition for `T_{|A|}`** (Definition 19.4.1 (2), read through the
uniformizers `Ψ̂ : E → A` of `F̂`, Proposition 19.7.23): every `e ∈ E` has an open `U(e) ∋ e` with
`cl_{|A|}(|Ψ̂(U(e))|) ⊂ |Ψ̂(E)|`. -/
def PropernessV2A (hP : IsFiniteToOneCovering P) (hC : Bh.IsCompatible)
    (hU : Bh.HasClassUniformizers) : Prop :=
  ∀ (x : Bh.hatU.Unif) (e : x.Ψh.ObjE),
    @Chapter19.OrbitChartV2 x.Ψh.ObjE _ A.OrbitSpace (Bh.natTopA hP hC hU)
      (fun d => A.π (x.Ψh.hat.obj d)) e

/-- `|P|(|Ψ̂(V)|) = |Ψ(τ̂(V))|`. -/
theorem image_orbitMap_imageA {β : B.Obj} (Ψh : CoveringUniformizer P β) (V : Set Ψh.ObjE) :
    P.orbitMap '' Ψh.imageA V = Ψh.imageB (Ψh.τ.obj '' V) := by
  ext z
  constructor
  · rintro ⟨_, ⟨e, he, rfl⟩, rfl⟩
    exact ⟨Ψh.τ.obj e, ⟨e, he, rfl⟩, (orbitMap_π_hat Ψh e).symm⟩
  · rintro ⟨_, ⟨e, he, rfl⟩, rfl⟩
    exact ⟨_, ⟨e, he, rfl⟩, orbitMap_π_hat Ψh e⟩

/-- **2021 Proposition 19.7.23, p. 923**, under `IsCompatible` and `HasClassUniformizers`:
`T_{|A|}` satisfies the properness condition (`PropernessV2A`) if and only if `T_{|B|}` does
(Definition 19.4.1 (2)).  (⇐) `|P|` is continuous and (19.34); (⇒) `|P|` is a closed map
(`isClosedMap_orbitMap`, Corollary 19.7.20 (2)). -/
theorem proposition_19_7_23_hyp (hP : IsFiniteToOneCovering P) (hC : Bh.IsCompatible)
    (hU : Bh.HasClassUniformizers) :
    Bh.PropernessV2A hP hC hU ↔ Bh.toBasic.PropernessV2 hU.toBasic := by
  let _ := Bh.natTopA hP hC hU
  let _ := Bh.toBasic.natTop hU.toBasic
  have hcont := Bh.continuous_orbitMap hP hC hU
  have hcl := Bh.isClosedMap_orbitMap hP hC hU
  constructor
  · rintro hA ⟨Ψ, α, Ψh, hΨh, rfl⟩ o
    set x : Bh.hatU.Unif := ⟨α, Ψh, hΨh⟩
    obtain ⟨e, rfl⟩ := Ψh.model.surjective o
    obtain ⟨V, hVo, heV, hVcl⟩ := hA x e
    refine ⟨Ψh.τ.obj '' V, Ψh.model.isLocalScDiffeo.isLocalHomeomorph.isOpenMap V hVo,
      ⟨e, heV, rfl⟩, ?_⟩
    change closure (Ψh.imageB (Ψh.τ.obj '' V)) ⊆ _
    rw [← image_orbitMap_imageA]
    refine (hcl.closure_image_subset _).trans ?_
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨d, rfl⟩ := hVcl hw
    exact ⟨Ψh.τ.obj d, (orbitMap_π_hat Ψh d).symm⟩
  · intro hB x e
    obtain ⟨U, hUo, hoU, hUcl⟩ := hB x.toUnif (x.Ψh.τ.obj e)
    refine ⟨x.Ψh.τ.obj ⁻¹' U, hUo.preimage x.Ψh.model.isLocalScDiffeo.isLocalHomeomorph.continuous,
      hoU, fun w hw => ?_⟩
    have hPw : P.orbitMap w ∈ closure (x.Ψh.imageB U) := by
      refine closure_mono ?_ (image_closure_subset_closure_image hcont ⟨w, hw, rfl⟩)
      rw [show (fun d => A.π (x.Ψh.hat.obj d)) '' (x.Ψh.τ.obj ⁻¹' U) =
        x.Ψh.imageA (x.Ψh.τ.obj ⁻¹' U) from rfl, image_orbitMap_imageA]
      exact image_mono (image_preimage_subset _ _)
    have h := (preimage_range_orbitMap hP x.Ψh).subset (hUcl hPw)
    exact h

/-! ### Proposition 19.7.24 -/

/-- **2021 Proposition 19.7.24, p. 924**, under `IsCompatible` and `HasClassUniformizers`:
`T_{|A|}` is paracompact if and only if `T_{|B|}` is.  `|P|` is continuous, open, surjective,
with finite fibres, and every open neighbourhood of `|P|⁻¹(z)` contains some `|P|⁻¹(W)`
(Corollary 19.7.20 (2)). -/
theorem proposition_19_7_24_hyp (hP : IsFiniteToOneCovering P) (hC : Bh.IsCompatible)
    (hU : Bh.HasClassUniformizers) :
    @ParacompactSpace _ (Bh.natTopA hP hC hU) ↔
      @ParacompactSpace _ (Bh.toBasic.natTop hU.toBasic) := by
  let _ := Bh.natTopA hP hC hU
  let _ := Bh.toBasic.natTop hU.toBasic
  have htube : ∀ (z : B.OrbitSpace) (U : Set A.OrbitSpace), IsOpen U → P.orbitMap ⁻¹' {z} ⊆ U →
      ∃ V, IsOpen V ∧ z ∈ V ∧ P.orbitMap ⁻¹' V ⊆ U := fun z _ hU' hsub =>
    Bh.exists_isOpen_preimage_subset hP hC hU z hU' hsub
  exact ⟨fun _ => Chapter19.paracompactSpace_of_tube_of_isOpenMap (Bh.continuous_orbitMap hP hC hU)
      (surjective_orbitMap hP) (Bh.isOpenMap_orbitMap hP hC hU) (finite_fiber_orbitMap hP) htube,
    fun _ => Chapter19.paracompactSpace_of_tube (Bh.continuous_orbitMap hP hC hU)
      (finite_fiber_orbitMap hP) htube⟩

/-! ### Theorem 19.7.25 -/

/-- `T_{|A|}` is Hausdorff when `T_{|B|}` is (the disjoint neighbourhoods of Corollary 19.7.20
(2)). -/
theorem t2Space_natTopA (hP : IsFiniteToOneCovering P) (hC : Bh.IsCompatible)
    (hU : Bh.HasClassUniformizers) (h2 : @T2Space _ (Bh.toBasic.natTop hU.toBasic)) :
    @T2Space _ (Bh.natTopA hP hC hU) := by
  let _ := Bh.natTopA hP hC hU
  let _ := Bh.toBasic.natTop hU.toBasic
  refine Chapter19.t2Space_of_disjoint_fibre_nhds (Bh.continuous_orbitMap hP hC hU) fun z => ?_
  obtain ⟨-, _, V, -, -, hV, hd, -⟩ := Bh.evenlyCovered_orbitMap hP hC hU z
  exact ⟨V, hV, hd⟩

/-- **`T_{|A|}` is locally metrizable** (Lemma 19.7.17 (1)): every point has an open metrizable
neighbourhood, the image of one in `|E|` (Theorem 7.3.1) under the open embedding `|Ψ̂|`. -/
theorem exists_metrizable_nhds_natTopA (hP : IsFiniteToOneCovering P) (hC : Bh.IsCompatible)
    (hU : Bh.HasClassUniformizers) (z : A.OrbitSpace) :
    ∃ W : Set A.OrbitSpace, IsOpen[Bh.natTopA hP hC hU] W ∧ z ∈ W ∧
      @MetrizableSpace W (@instTopologicalSpaceSubtype _ _ (Bh.natTopA hP hC hU)) := by
  let _ := Bh.natTopA hP hC hU
  obtain ⟨-, h⟩ := Bh.lemma_19_7_17_one_hyp hP hC hU
  obtain ⟨x, ⟨w, rfl⟩, hj⟩ := h z
  obtain ⟨V, hVo, hwV, hVm⟩ := (x.Ψh.E.theorem_7_3_1).1 w
  refine ⟨x.Ψh.hat.orbitMap '' V, hj.isOpenMap V hVo, ⟨w, hwV, rfl⟩, ?_⟩
  have hemb : IsEmbedding (fun v : V => x.Ψh.hat.orbitMap v) :=
    hj.isEmbedding.comp IsEmbedding.subtypeVal
  have hrange : range (fun v : V => x.Ψh.hat.orbitMap v) = x.Ψh.hat.orbitMap '' V :=
    (image_eq_range _ _).symm
  have hm : MetrizableSpace (range fun v : V => x.Ψh.hat.orbitMap v) :=
    hemb.toHomeomorph.symm.isEmbedding.metrizableSpace
  rw [hrange] at hm
  exact hm

/-- **2021 Theorem 19.7.25 (1), p. 925**, under `IsCompatible` and `HasClassUniformizers`: if
`T_{|B|}` is metrizable, then `T_{|A|}` is metrizable and `|P| : |A| → |B|` is a surjective
continuous map.  `T_{|A|}` is paracompact (Proposition 19.7.24), Hausdorff (`t2Space_natTopA`)
and locally metrizable, hence metrizable (`metrizableSpace_of_locally`, i.e.
`metrizableSpace_of_pullback` along `id`). -/
theorem theorem_19_7_25_one_hyp (hP : IsFiniteToOneCovering P) (hC : Bh.IsCompatible)
    (hU : Bh.HasClassUniformizers) (hm : @MetrizableSpace _ (Bh.toBasic.natTop hU.toBasic)) :
    @MetrizableSpace _ (Bh.natTopA hP hC hU) ∧
      Continuous[Bh.natTopA hP hC hU, Bh.toBasic.natTop hU.toBasic] P.orbitMap ∧
      Surjective P.orbitMap := by
  let _ := Bh.natTopA hP hC hU
  let _ := Bh.toBasic.natTop hU.toBasic
  have : ParacompactSpace B.OrbitSpace := paracompactSpace_of_metrizableSpace _
  have : ParacompactSpace A.OrbitSpace := (Bh.proposition_19_7_24_hyp hP hC hU).2 this
  have : T2Space A.OrbitSpace := Bh.t2Space_natTopA hP hC hU inferInstance
  exact ⟨metrizableSpace_of_locally (Bh.exists_metrizable_nhds_natTopA hP hC hU),
    Bh.continuous_orbitMap hP hC hU, surjective_orbitMap hP⟩

/-- **The GCT `A`** (Theorem 19.7.25 (2)): `A` with `T_{|A|}`, metrizable if `T_{|B|}` is. -/
def toGCTA (hP : IsFiniteToOneCovering P) (hC : Bh.IsCompatible)
    (hU : Bh.HasClassUniformizers) (hm : @MetrizableSpace _ (Bh.toBasic.natTop hU.toBasic)) :
    GCT.{u} where
  toGroupoidalCategory := A
  top := Bh.natTopA hP hC hU
  metrizable := (Bh.theorem_19_7_25_one_hyp hP hC hU hm).1

/-- **The GCT `B`** (Theorem 19.7.25 (2)): `B` with the metrizable `T_{|B|}`. -/
def toGCTB (hU : Bh.HasClassUniformizers)
    (hm : @MetrizableSpace _ (Bh.toBasic.natTop hU.toBasic)) : GCT.{u} where
  toGroupoidalCategory := B
  top := Bh.toBasic.natTop hU.toBasic
  metrizable := hm

/-- **2021 Theorem 19.7.25 (2), p. 926**, under `IsCompatible` and `HasClassUniformizers`: if
`T_{|B|}` is metrizable, `A` and `B` with their natural topologies are GCTs (`toGCTA`,
`toGCTB`). -/
theorem theorem_19_7_25_two_hyp (hP : IsFiniteToOneCovering P) (hC : Bh.IsCompatible)
    (hU : Bh.HasClassUniformizers) (hm : @MetrizableSpace _ (Bh.toBasic.natTop hU.toBasic)) :
    (Bh.toGCTA hP hC hU hm).toGroupoidalCategory = A ∧
      (Bh.toGCTA hP hC hU hm).top = Bh.natTopA hP hC hU ∧
      (Bh.toGCTB hU hm).toGroupoidalCategory = B ∧
      (Bh.toGCTB hU hm).top = Bh.toBasic.natTop hU.toBasic ∧
      @MetrizableSpace _ (Bh.natTopA hP hC hU) ∧ @MetrizableSpace _ (Bh.toBasic.natTop hU.toBasic) :=
  ⟨rfl, rfl, rfl, rfl, (Bh.theorem_19_7_25_one_hyp hP hC hU hm).1, hm⟩

/-- **2021 Theorem 19.7.25 (3), p. 926**, under `IsCompatible` and `HasClassUniformizers`: if
`T_{|B|}` is metrizable, `P : A → B` is a proper covering functor of GCTs (Definition 17.8.1). -/
theorem theorem_19_7_25_three_hyp (hP : IsFiniteToOneCovering P) (hC : Bh.IsCompatible)
    (hU : Bh.HasClassUniformizers) (hm : @MetrizableSpace _ (Bh.toBasic.natTop hU.toBasic)) :
    @GroupoidFunctor.IsProperCoveringGCT (Bh.toGCTA hP hC hU hm) (Bh.toGCTB hU hm) P where
  continuous_orbitMap := Bh.continuous_orbitMap hP hC hU
  surjective_orbitMap := surjective_orbitMap hP
  finite_fiber := hP.finite_fiber
  surjective_obj := hP.surjective
  evenlyCovered := Bh.evenlyCovered_orbitMap hP hC hU
  bijective_fibredMor := hP.bijective

/-- **2021 Theorem 19.7.25 (4a), p. 926**, under `IsCompatible` and `HasClassUniformizers`: for
every `z ∈ |B|` the preimage `|P|⁻¹(z)` is finite, and there are an open neighbourhood `U(z)` and
mutually disjoint open neighbourhoods `U(z̄)` of the `z̄ ∈ |P|⁻¹(z)` with
`|P|⁻¹(U(z)) = ⋃ U(z̄)`.  (The metrizability of `T_{|B|}` is not needed.) -/
theorem theorem_19_7_25_four_a_hyp (hP : IsFiniteToOneCovering P) (hC : Bh.IsCompatible)
    (hU : Bh.HasClassUniformizers) (z : B.OrbitSpace) :
    (P.orbitMap ⁻¹' {z}).Finite ∧
      ∃ (Uz : Set B.OrbitSpace) (V : A.OrbitSpace → Set A.OrbitSpace),
        IsOpen[Bh.toBasic.natTop hU.toBasic] Uz ∧ z ∈ Uz ∧
        (∀ y ∈ P.orbitMap ⁻¹' {z}, IsOpen[Bh.natTopA hP hC hU] (V y) ∧ y ∈ V y) ∧
        (P.orbitMap ⁻¹' {z}).PairwiseDisjoint V ∧
        P.orbitMap ⁻¹' Uz = ⋃ y ∈ P.orbitMap ⁻¹' {z}, V y :=
  Bh.evenlyCovered_orbitMap hP hC hU z

end CoveringBasicConstruction

end GroupoidalCategory

end Polyfold
