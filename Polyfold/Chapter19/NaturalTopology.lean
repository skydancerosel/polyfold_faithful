import Polyfold.Chapter19.BasicConstruction
import Polyfold.Chapter19.TopologyLemmas

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 19,
§19.2 "The Natural Topology T for |S|" (pp. 869–872) and §19.3 "The Natural Topology for
M(Ψ,Ψ′)" (pp. 872–879): **Definition 19.2.1**, **Theorem 19.2.2**, **Remark 19.2.4**,
**Lemma 19.3.1**, **Definition 19.3.2**, **Theorem 19.3.3**, **Proposition 19.3.4**,
**Proposition 19.3.5**, **Remark 19.3.6**, **Proposition 19.3.7**, **Lemma 19.3.8**.  (Remark 19.2.3
and the counterexample to Theorem 19.2.2 (1) as we read it are in `BasicConstructionExamples`.)
Numbers and pages are the 2021 text's.

# The natural topologies of a basic construction

## The text, paraphrased

(19.2.1) `T` consists of the `U ⊂ |S|` such that every `z ∈ U` has an `α_z` with `|α_z| = z`,
`Ψ ∈ F(α_z)`, `Ψ(ō) = α_z` and an open `V(ō)` with `|Ψ(V(ō))| ⊂ U`.  (19.2.2) (1) `T` is a topology;
(2) `|Ψ(V)|` is open for open `V ⊂ O`; (3) `|Ψ| : G\O → |S|` is a homeomorphism onto an open
neighbourhood of `|α|`; (4) first countable; (5) locally metrizable.  (19.2.4) If `T` is
Hausdorff, regular and second countable, `(S, T)` is a GCT.
(19.3.1) For a representative `F` of `𝓕`, `T^F_{Ψ,Ψ'}` consists of the `W ⊂ M(Ψ, Ψ')` such that
every `h ∈ W` has an open `V ∋ o` with `F_h(V) ⊂ W`; it does not depend on `F`.  (19.3.2) This is
`T_{Ψ,Ψ'}`.  (19.3.4) It is a topology; (1) `F_h(W)` is open; (2) `F_h` is continuous, a
homeomorphism onto an open set; (3) Hausdorff (by (F)).  (19.3.5) `s`, `t` local homeomorphisms,
`u` continuous, `ι` a homeomorphism, `m` continuous.  (19.3.6) (a) `u` is an open embedding;
(b) `m` is a local homeomorphism.  (19.3.7) `Ψ̄ : G × O → M(Ψ, Ψ)` is a homeomorphism.
(19.3.8) `T_{Ψ,Ψ'}` is regular.  (19.3.3) All of this: a regular Hausdorff locally metrizable
topology with (1)–(6).

## What is formalized

* `UniformizerConstruction.NatOpen` (**Definition 19.2.1**); `natOpen_empty`, `natOpen_sUnion`,
  `natOpen_inter` (unconditional), `natOpen_univ_iff` (`|S| ∈ T` iff every isomorphism class
  contains an `α` with `F(α) ≠ ∅`).
* `BasicConstruction.natTop hB` (the topology `T`, for `hB : U.HasClassUniformizers`);
  **Theorem 19.2.2**: `theorem_19_2_2_one`, `theorem_19_2_2_two`,
  `theorem_19_2_2_three`, `theorem_19_2_2_four`, `theorem_19_2_2_five`, and
  `isOrbitChart` (`o ↦ |Ψ(o)|` is an orbit chart of Chapter 19's `TopologyLemmas`).
  **Remark 19.2.4**: `remark_19_2_4` (metrizable by Urysohn) and `toGCT`.
* `TransitionData.IsOpenTr` (`T^F_{Ψ,Ψ'}`), `TransitionData.topology` and the type synonym
  `TransitionData.Tr` carrying it; **Lemma 19.3.1** `lemma_19_3_1`;
  `TransitionConstruction.topology` (**Definition 19.3.2**, by `Quotient.lift`),
  `BasicConstruction.M Ψ Ψ'` (`M(Ψ, Ψ')` with `T_{Ψ,Ψ'}`), `definition_19_3_2`,
  `isOpen_M_iff`, `trHomeomorph`.
* For any transition data: `isOpen_image_map`, `continuousAt_map`, `continuousOn_map`, `sheet`
  (`F_h` as an open partial homeomorphism with inverse `s`), `continuous_src`, `t2Space`,
  `isLocalHomeomorph_src`, `continuous_inv`, `invHomeomorph`, `isLocalHomeomorph_tgt`,
  `continuous_unit`, `continuous_mulMap`, `isOpenEmbedding_unit`, `isLocalHomeomorph_mulMap`,
  `hatHomeomorph`, `regularSpace`, `exists_isOpen_metrizableSpace`.
* Item-numbered statements on `B.M Ψ Ψ'`: `proposition_19_3_4_topology`, `proposition_19_3_4`,
  `proposition_19_3_5`, `remark_19_3_6_a`, `remark_19_3_6_b`, `proposition_19_3_7`, `lemma_19_3_8`,
  `theorem_19_3_3`.

## Readings

* Theorem 19.2.2 (1)–(5) are stated under `F(α) ≠ ∅`, the standing reading of §17.1, in the form
  that every isomorphism class contains an object `α` with `F(α) ≠ ∅` (`HasClassUniformizers`):
  the proof calls `|S| ∈ T` clear, and the proof of (2) picks `Ψ' ∈ F(α')` for an arbitrary `α'`.
  Without it `|S| ∉ T` (`natOpen_univ_iff`); with `F ≡ ∅` on a non-empty `S`, `T = {∅}`
  (`theorem_19_2_2_empty_family`).  The closure of `T` under unions and finite non-empty
  intersections holds without it.
* Theorem 19.2.2 (3) "a homeomorphism onto an open neighbourhood of `|α|`" is `IsOpenEmbedding |Ψ|`
  with `|α|` in the range; (4) is `FirstCountableTopology`; (5) is "every point has an open
  metrizable neighbourhood".
* Remark 19.2.4: "Hausdorff, regular, second countable ⇒ GCT" through Urysohn's metrization
  theorem (Mathlib's `metrizableSpace_of_t3_secondCountable`).
* Lemma 19.3.1 is stated for equivalent transition data (`F₁ ≈ F₂`), i.e. two representatives
  of one class; Definition 19.3.2 is then a `Quotient.lift`.  The type `B.M Ψ Ψ'` carries the
  topology of the chosen representative `B.rep`, which is `T_{Ψ,Ψ'}` (`definition_19_3_2`).
* "`Fh : V(o) → Fh(V(o))` is a homeomorphism" (19.3.4 (2)) is
  `IsOpenEmbedding (V(o).restrict F_h)`; the domain of `m` is the fibred product
  `{(h', h) | s(h') = t(h)}` with the subspace topology of the product (`FibProd`), and `m` is
  `TransitionSet.comp` there (`mulMap`, equal to Chapter 17's `TransitionSet.mul`).
* Proposition 19.3.7: the proof's step "`s ∘ Ψ̄` and `s` are local homeomorphisms, hence `Ψ̄` is"
  needs the continuity of `Ψ̄`, which we take from the special form of (A)
  (`F_{(o,Ψ(g,o),g∗o)}(q) = Ψ̄(g, q)`); Chapter 17's `not_lemma_17_1_9` shows that it does not come
  for free.
* Lemma 19.3.8: the text's sequence argument ends with "`W(h) ∩ A = ∅`", which is a choice of
  `W(h)`; we use `regularSpace_of_isLocalHomeomorph_of_t2` (Chapter 19 `TopologyLemmas`), where
  this choice is made.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter TopologicalSpace

noncomputable section

namespace Polyfold

universe u

namespace GroupoidalCategory

variable {C : GroupoidalCategory.{u}}

/-! ### §19.2: the natural topology `T` on `|S|` -/

namespace UniformizerConstruction

variable (U : C.UniformizerConstruction)

/-- **2021 Definition 19.2.1, p. 869**: the collection `T`: `W ⊂ |S|` belongs to `T` if every
`z ∈ W` has an object `α` with `|α| = z`, a `Ψ ∈ F(α)`, `ō` with `Ψ(ō) = α` and an open
`V ∋ ō` with `|Ψ(V)| ⊂ W`. -/
def NatOpen (W : Set C.OrbitSpace) : Prop :=
  ∀ z ∈ W, ∃ α, C.π α = z ∧ ∃ Ψ ∈ U.F α, ∃ o : Ψ.O, Ψ.obj o = α ∧
    ∃ V : Set Ψ.O, IsOpen V ∧ o ∈ V ∧ (fun q => C.π (Ψ.obj q)) '' V ⊆ W

theorem natOpen_empty : U.NatOpen ∅ := fun _ hz => absurd hz (notMem_empty _)

theorem natOpen_sUnion {S : Set (Set C.OrbitSpace)} (hS : ∀ W ∈ S, U.NatOpen W) :
    U.NatOpen (⋃₀ S) := by
  rintro z ⟨W, hW, hz⟩
  obtain ⟨α, hα, Ψ, hΨ, o, ho, V, hV, hoV, hsub⟩ := hS W hW z hz
  exact ⟨α, hα, Ψ, hΨ, o, ho, V, hV, hoV, hsub.trans (subset_sUnion_of_mem hW)⟩

/-- `|S| ∈ T` iff every isomorphism class contains an object `α` with `F(α) ≠ ∅`. -/
theorem natOpen_univ_iff : U.NatOpen univ ↔ U.HasClassUniformizers := by
  constructor
  · intro h z
    obtain ⟨α, hα, Ψ, hΨ, -⟩ := h z (mem_univ z)
    exact ⟨α, hα, Ψ, hΨ⟩
  · intro h z _
    obtain ⟨α, hα, Ψ, hΨ⟩ := h z
    obtain ⟨o, ho⟩ := U.isAt α Ψ hΨ
    exact ⟨α, hα, Ψ, hΨ, o, ho, univ, isOpen_univ, mem_univ _, subset_univ _⟩

/-- **The proof of Theorem 19.2.2 (1), finite intersections** (p. 870): for `z ∈ W₁ ∩ W₂` with
`|Ψ₁(V₁)| ⊂ W₁`, `|Ψ₂(V₂)| ⊂ W₂`, take `h = (ō₁, φ, ō₂) ∈ M(Ψ₁, Ψ₂)` and shrink `V₁` so that
`f_h(V₁) ⊂ V₂`. -/
theorem natOpen_inter (F : U.TransitionData) {W₁ W₂ : Set C.OrbitSpace} (h₁ : U.NatOpen W₁)
    (h₂ : U.NatOpen W₂) : U.NatOpen (W₁ ∩ W₂) := by
  rintro z ⟨hz₁, hz₂⟩
  obtain ⟨α₁, hα₁, Ψ₁, hΨ₁, o₁, ho₁, V₁, hV₁, hoV₁, hsub₁⟩ := h₁ z hz₁
  obtain ⟨α₂, hα₂, Ψ₂, hΨ₂, o₂, ho₂, V₂, hV₂, hoV₂, hsub₂⟩ := h₂ z hz₂
  obtain ⟨φ, hφs, hφt⟩ := (C.π_eq_π_iff).1 (hα₁.trans hα₂.symm)
  let P₁ : U.Unif := ⟨Ψ₁, α₁, hΨ₁⟩
  let P₂ : U.Unif := ⟨Ψ₂, α₂, hΨ₂⟩
  let h : P₁.1.Trans P₂.1 := ⟨o₁, φ, o₂, hφs.trans ho₁.symm, hφt.trans ho₂.symm⟩
  obtain ⟨N, hN, hoN, hNs, hNf⟩ := F.exists_nbhd_fmap P₁ P₂ h hV₂ hoV₂
  refine ⟨α₁, hα₁, Ψ₁, hΨ₁, o₁, ho₁, N ∩ V₁, hN.inter hV₁, ⟨hoN, hoV₁⟩, ?_⟩
  rintro _ ⟨q, ⟨hqN, hqV⟩, rfl⟩
  refine ⟨hsub₁ ⟨q, hqV, rfl⟩, ?_⟩
  change C.π (Ψ₁.obj q) ∈ W₂
  rw [show C.π (Ψ₁.obj q) = C.π (Ψ₂.obj (F.fmap P₁ P₂ h q)) from F.π_obj_eq P₁ P₂ h (hNs hqN)]
  exact hsub₂ ⟨_, hNf q hqN, rfl⟩

end UniformizerConstruction

namespace BasicConstruction

variable (B : C.BasicConstruction)

/-- **The natural topology `T` on `|S|`** (Definition 19.2.1, Theorem 19.2.2 (1)), when every
isomorphism class contains an object with a uniformizer. -/
abbrev natTop (hB : B.U.HasClassUniformizers) : TopologicalSpace C.OrbitSpace where
  IsOpen := B.U.NatOpen
  isOpen_univ := B.U.natOpen_univ_iff.2 hB
  isOpen_inter _ _ := B.U.natOpen_inter B.rep
  isOpen_sUnion _ := B.U.natOpen_sUnion

theorem isOpen_natTop_iff (hB : B.U.HasClassUniformizers) {W : Set C.OrbitSpace} :
    IsOpen[B.natTop hB] W ↔ B.U.NatOpen W := Iff.rfl

/-- **2021 Theorem 19.2.2 (1), p. 869**, under `HasClassUniformizers` (`F(α) ≠ ∅`, the standing
reading of §17.1): `T` is a topology on `|S|` (`|S| ∈ T`, finite intersections, arbitrary
unions). -/
theorem theorem_19_2_2_one (hB : B.U.HasClassUniformizers) :
    B.U.NatOpen univ ∧ (∀ W₁ W₂, B.U.NatOpen W₁ → B.U.NatOpen W₂ → B.U.NatOpen (W₁ ∩ W₂)) ∧
      ∀ S : Set (Set C.OrbitSpace), (∀ W ∈ S, B.U.NatOpen W) → B.U.NatOpen (⋃₀ S) :=
  ⟨B.U.natOpen_univ_iff.2 hB, fun _ _ => B.U.natOpen_inter B.rep, fun _ => B.U.natOpen_sUnion⟩

/-- **2021 Theorem 19.2.2 (2), p. 869**, under `HasClassUniformizers` (`F(α) ≠ ∅`, the standing
reading of §17.1): for `Ψ ∈ F(α)` and open `V ⊂ O`, `|Ψ(V)|` is open in `T`. -/
theorem theorem_19_2_2_two (hB : B.U.HasClassUniformizers) {α : C.Obj} {Ψ : C.Uniformizer}
    (hΨ : Ψ ∈ B.U.F α) {V : Set Ψ.O} (hV : IsOpen V) :
    IsOpen[B.natTop hB] ((fun q => C.π (Ψ.obj q)) '' V) := by
  rintro _ ⟨o, hoV, rfl⟩
  obtain ⟨α', hα', Ψ', hΨ'⟩ := hB (C.π (Ψ.obj o))
  obtain ⟨o', ho'⟩ := B.U.isAt α' Ψ' hΨ'
  obtain ⟨φ, hφs, hφt⟩ := (C.π_eq_π_iff).1 hα'
  let P : B.U.Unif := ⟨Ψ, α, hΨ⟩
  let P' : B.U.Unif := ⟨Ψ', α', hΨ'⟩
  let h : P'.1.Trans P.1 := ⟨o', φ, o, hφs.trans ho'.symm, hφt⟩
  obtain ⟨N, hN, hoN, hNs, hNf⟩ := B.rep.exists_nbhd_fmap P' P h hV hoV
  refine ⟨α', hα', Ψ', hΨ', o', ho', N, hN, hoN, ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  exact ⟨_, hNf q hq, (B.rep.π_obj_eq P' P h (hNs hq)).symm⟩

/-- `o ↦ |Ψ(o)|` is continuous `O → (|S|, T)` (the continuity step of Theorem 19.2.2 (3)). -/
theorem continuous_π_obj (hB : B.U.HasClassUniformizers) {α : C.Obj} {Ψ : C.Uniformizer}
    (hΨ : Ψ ∈ B.U.F α) : Continuous[_, B.natTop hB] fun q : Ψ.O => C.π (Ψ.obj q) := by
  let _inst := B.natTop hB
  refine continuous_def.2 fun W hW => isOpen_iff_forall_mem_open.2 fun q hq => ?_
  obtain ⟨α', hα', Ψ', hΨ', o', ho', V', hV', hoV', hsub'⟩ := hW _ hq
  obtain ⟨φ, hφs, hφt⟩ := (C.π_eq_π_iff).1 hα'.symm
  let P : B.U.Unif := ⟨Ψ, α, hΨ⟩
  let P' : B.U.Unif := ⟨Ψ', α', hΨ'⟩
  let h : P.1.Trans P'.1 := ⟨q, φ, o', hφs, hφt.trans ho'.symm⟩
  obtain ⟨N, hN, hqN, hNs, hNf⟩ := B.rep.exists_nbhd_fmap P P' h hV' hoV'
  refine ⟨N, fun p hp => ?_, hN, hqN⟩
  change C.π (Ψ.obj p) ∈ W
  rw [show C.π (Ψ.obj p) = C.π (Ψ'.obj (B.rep.fmap P P' h p)) from
    B.rep.π_obj_eq P P' h (hNs hp)]
  exact hsub' ⟨_, hNf p hp, rfl⟩

/-- **2021 Theorem 19.2.2 (3), p. 869**, under `HasClassUniformizers` (`F(α) ≠ ∅`, the standing
reading of §17.1): for `Ψ ∈ F(α)`, `|Ψ| : G\O → |S|` is a homeomorphism onto an open neighbourhood
of `|α|`. -/
theorem theorem_19_2_2_three (hB : B.U.HasClassUniformizers) {α : C.Obj} {Ψ : C.Uniformizer}
    (hΨ : Ψ ∈ B.U.F α) :
    @IsOpenEmbedding _ _ _ (B.natTop hB) Ψ.functor.orbitMap ∧ C.π α ∈ range Ψ.functor.orbitMap := by
  let _inst := B.natTop hB
  refine ⟨IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_, ?_⟩
  · exact continuous_coinduced_dom.2 (B.continuous_π_obj hB hΨ)
  · intro x y hxy
    induction x using Quotient.inductionOn with | h q => ?_
    induction y using Quotient.inductionOn with | h q' => ?_
    obtain ⟨φ, hs, ht⟩ := (C.π_eq_π_iff).1 hxy
    obtain ⟨g, hg, -⟩ := Ψ.exists_smul_eq_mor hs ht
    exact (GroupoidStr.π_eq_π_iff _).2 ⟨(g, q), rfl, hg⟩
  · intro A hA
    have : Ψ.functor.orbitMap '' A =
        (fun q => C.π (Ψ.obj q)) '' ((GroupoidStr.translation Ψ.G Ψ.O).π ⁻¹' A) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        induction w using Quotient.inductionOn with | h q => exact ⟨q, hw, rfl⟩
      · rintro ⟨q, hq, rfl⟩
        exact ⟨_, hq, rfl⟩
    rw [this]
    exact B.theorem_19_2_2_two hB hΨ (hA.preimage continuous_quot_mk)
  · obtain ⟨o, ho⟩ := B.U.isAt α Ψ hΨ
    exact ⟨(GroupoidStr.translation Ψ.G Ψ.O).π o, by rw [← ho]; rfl⟩

/-- `o ↦ |Ψ(o)|` is an orbit chart of `G` (continuous, open, fibres the `G`-orbits), in the sense
of Chapter 19's `TopologyLemmas` (for the metrizability criteria of §19.4). -/
theorem isOrbitChart (hB : B.U.HasClassUniformizers) {α : C.Obj} {Ψ : C.Uniformizer}
    (hΨ : Ψ ∈ B.U.F α) :
    @Chapter19.IsOrbitChart Ψ.G _ Ψ.O _ _ C.OrbitSpace (B.natTop hB)
      (fun q => C.π (Ψ.obj q)) := by
  let _inst := B.natTop hB
  refine ⟨B.continuous_π_obj hB hΨ, fun V hV => B.theorem_19_2_2_two hB hΨ hV,
    fun x y => ⟨fun hxy => ?_, ?_⟩⟩
  · obtain ⟨φ, hs, ht⟩ := (C.π_eq_π_iff).1 hxy
    obtain ⟨g, hg, -⟩ := Ψ.exists_smul_eq_mor hs ht
    exact ⟨g, hg⟩
  · rintro ⟨g, rfl⟩
    exact (C.π_eq_π_iff).2 ⟨Ψ.mor (g, x), Ψ.src_mor _, Ψ.tgt_mor _⟩

/-- **2021 Theorem 19.2.2 (5), p. 869**, under `HasClassUniformizers` (`F(α) ≠ ∅`, the standing
reading of §17.1): every point of `|S|` has an open metrizable neighbourhood (the image of `|Ψ|`,
homeomorphic to the metrizable `G\O`). -/
theorem theorem_19_2_2_five (hB : B.U.HasClassUniformizers) (z : C.OrbitSpace) :
    ∃ W : Set C.OrbitSpace, IsOpen[B.natTop hB] W ∧ z ∈ W ∧
      @MetrizableSpace W (@instTopologicalSpaceSubtype _ _ (B.natTop hB)) := by
  let _inst := B.natTop hB
  obtain ⟨α, rfl, Ψ, hΨ⟩ := hB z
  obtain ⟨he, hα⟩ := B.theorem_19_2_2_three hB hΨ
  have := metrizableSpace_translation_orbitSpace Ψ.smooth_smul
  exact ⟨_, he.isOpen_range, hα, he.isEmbedding.toHomeomorph.symm.isEmbedding.metrizableSpace⟩

/-- **2021 Theorem 19.2.2 (4), p. 869**, under `HasClassUniformizers` (`F(α) ≠ ∅`, the standing
reading of §17.1): every point of `|S|` has a countable neighbourhood basis. -/
theorem theorem_19_2_2_four (hB : B.U.HasClassUniformizers) :
    @FirstCountableTopology C.OrbitSpace (B.natTop hB) := by
  let _inst := B.natTop hB
  refine ⟨fun z => ?_⟩
  obtain ⟨α, hα, Ψ, hΨ⟩ := hB z
  obtain ⟨he, x, hx⟩ := B.theorem_19_2_2_three hB hΨ
  have := metrizableSpace_translation_orbitSpace Ψ.smooth_smul
  rw [← hα, ← hx, ← he.map_nhds_eq x]
  infer_instance

/-- **2021 Remark 19.2.4, p. 872**: if `T` is Hausdorff, regular and second countable, it is
metrizable (Urysohn), so `(S, T)` is a GCT (`toGCT`). -/
theorem remark_19_2_4 (hB : B.U.HasClassUniformizers) (h₂ : @T2Space _ (B.natTop hB))
    (h₃ : @RegularSpace _ (B.natTop hB)) (h₄ : @SecondCountableTopology _ (B.natTop hB)) :
    @MetrizableSpace C.OrbitSpace (B.natTop hB) := by
  let _inst := B.natTop hB
  exact metrizableSpace_of_t3_secondCountable _

/-- **2021 Remark 19.2.4, p. 872**: the GCT `(S, T)` of a basic construction whose natural
topology is Hausdorff, regular and second countable (Definition 17.1.1). -/
def toGCT (hB : B.U.HasClassUniformizers) (h₂ : @T2Space _ (B.natTop hB))
    (h₃ : @RegularSpace _ (B.natTop hB)) (h₄ : @SecondCountableTopology _ (B.natTop hB)) :
    GCT.{u} where
  toGroupoidalCategory := C
  top := B.natTop hB
  metrizable := B.remark_19_2_4 hB h₂ h₃ h₄

end BasicConstruction

/-! ### §19.3: the natural topology on `M(Ψ, Ψ')` -/

namespace UniformizerConstruction

namespace TransitionData

open GroupoidStr (TransitionSet)
open GroupoidStr.TransitionSet (src_inv tgt_inv inv_inv src_comp tgt_comp)

variable {U : C.UniformizerConstruction} (F : U.TransitionData)

/-- **The collection `T^F_{Ψ,Ψ'}` of 2021 Lemma 19.3.1, p. 872**: `W ⊂ M(Ψ, Ψ')` such that every
`h ∈ W` has an open `V ∋ s(h)` inside `V(o)` with `F_h(V) ⊂ W`. -/
def IsOpenTr (Ψ Ψ' : U.Unif) (W : Set (Ψ.1.Trans Ψ'.1)) : Prop :=
  ∀ h ∈ W, ∃ V : Set Ψ.1.O, IsOpen V ∧ h.src ∈ V ∧ V ⊆ F.dom Ψ Ψ' h ∧ F.map Ψ Ψ' h '' V ⊆ W

/-- **2021 Proposition 19.3.4, p. 874, first assertion**: `T^F_{Ψ,Ψ'}` is a topology. -/
theorem isOpenTr_topology (Ψ Ψ' : U.Unif) :
    F.IsOpenTr Ψ Ψ' univ ∧
      (∀ W₁ W₂, F.IsOpenTr Ψ Ψ' W₁ → F.IsOpenTr Ψ Ψ' W₂ → F.IsOpenTr Ψ Ψ' (W₁ ∩ W₂)) ∧
      ∀ S : Set (Set (Ψ.1.Trans Ψ'.1)), (∀ W ∈ S, F.IsOpenTr Ψ Ψ' W) → F.IsOpenTr Ψ Ψ' (⋃₀ S) := by
  refine ⟨fun h _ => ⟨F.dom Ψ Ψ' h, F.isOpen_dom _ _ _, F.mem_dom _ _ _, subset_rfl,
    subset_univ _⟩, fun W₁ W₂ h₁ h₂ h hh => ?_, fun S hS h hh => ?_⟩
  · obtain ⟨V₁, hV₁, ho₁, hs₁, hi₁⟩ := h₁ h hh.1
    obtain ⟨V₂, hV₂, ho₂, -, hi₂⟩ := h₂ h hh.2
    exact ⟨V₁ ∩ V₂, hV₁.inter hV₂, ⟨ho₁, ho₂⟩, inter_subset_left.trans hs₁,
      subset_inter ((image_mono inter_subset_left).trans hi₁)
        ((image_mono inter_subset_right).trans hi₂)⟩
  · obtain ⟨W, hW, hhW⟩ := hh
    obtain ⟨V, hV, ho, hs, hi⟩ := hS W hW h hhW
    exact ⟨V, hV, ho, hs, hi.trans (subset_sUnion_of_mem hW)⟩

/-- The topology `T^F_{Ψ,Ψ'}` on `M(Ψ, Ψ')` (Proposition 19.3.4). -/
abbrev topology (Ψ Ψ' : U.Unif) : TopologicalSpace (Ψ.1.Trans Ψ'.1) where
  IsOpen := F.IsOpenTr Ψ Ψ'
  isOpen_univ := (F.isOpenTr_topology Ψ Ψ').1
  isOpen_inter := (F.isOpenTr_topology Ψ Ψ').2.1
  isOpen_sUnion := (F.isOpenTr_topology Ψ Ψ').2.2

/-- `M(Ψ, Ψ')` with the topology `T^F_{Ψ,Ψ'}`. -/
def Tr (_F : U.TransitionData) (Ψ Ψ' : U.Unif) : Type u := Ψ.1.Trans Ψ'.1

instance (Ψ Ψ' : U.Unif) : TopologicalSpace (F.Tr Ψ Ψ') := F.topology Ψ Ψ'

theorem isOpen_tr_iff {Ψ Ψ' : U.Unif} {W : Set (F.Tr Ψ Ψ')} : IsOpen W ↔ F.IsOpenTr Ψ Ψ' W :=
  Iff.rfl

theorem isOpenTr_of_equiv {F₁ F₂ : U.TransitionData} (e : F₁.Equiv F₂) {Ψ Ψ' : U.Unif}
    {W : Set (Ψ.1.Trans Ψ'.1)} (hW : F₁.IsOpenTr Ψ Ψ' W) : F₂.IsOpenTr Ψ Ψ' W := by
  intro h hh
  obtain ⟨V, hV, ho, -, hi⟩ := hW h hh
  obtain ⟨V', hV', ho', hs', he⟩ := e Ψ Ψ' h
  refine ⟨V ∩ V', hV.inter hV', ⟨ho, ho'⟩, fun q hq => (hs' hq.2).2, ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  rw [← he hq.2]
  exact hi ⟨q, hq.1, rfl⟩

/-- **2021 Lemma 19.3.1, p. 872**: two representatives `F₁`, `F₂` of a transition construction
(equivalent transition data) give the same collection: `T^{F₁}_{Ψ,Ψ'} = T^{F₂}_{Ψ,Ψ'}`. -/
theorem lemma_19_3_1 {F₁ F₂ : U.TransitionData} (e : F₁.Equiv F₂) (Ψ Ψ' : U.Unif) :
    F₁.IsOpenTr Ψ Ψ' = F₂.IsOpenTr Ψ Ψ' :=
  funext fun _ => propext ⟨isOpenTr_of_equiv e, isOpenTr_of_equiv e.symm⟩

/-- An element of `M(Ψ, Ψ')` regarded in `F.Tr Ψ Ψ'` (with the topology `T^F_{Ψ,Ψ'}`). -/
abbrev toTr {Ψ Ψ' : U.Unif} (a : Ψ.1.Trans Ψ'.1) : F.Tr Ψ Ψ' := a

/-- Composites of tuples of `M(Ψ, Ψ')` depend only on the tuples. -/
theorem comp_congr {Ψ Ψ' Ψ'' : U.Unif} {a a' : Ψ'.1.Trans Ψ''.1} {b b' : Ψ.1.Trans Ψ'.1}
    (ha : a = a') (hb : b = b') (hab : C.toGroupoidStr.src a.mor = C.toGroupoidStr.tgt b.mor)
    (hab' : C.toGroupoidStr.src a'.mor = C.toGroupoidStr.tgt b'.mor) :
    TransitionSet.comp a b hab = TransitionSet.comp a' b' hab' := by
  subst ha hb
  rfl

section Sheets

variable (Ψ Ψ' : U.Unif)

/-- **2021 Proposition 19.3.4 (1), p. 874**: for open `W ⊂ V(o)`, `F_h(W)` is open (by (B)). -/
theorem isOpen_image_map (h : Ψ.1.Trans Ψ'.1) {W : Set Ψ.1.O} (hW : IsOpen W)
    (hWs : W ⊆ F.dom Ψ Ψ' h) : IsOpen (X := F.Tr Ψ Ψ') (F.map Ψ Ψ' h '' W) := by
  rintro _ ⟨q, hqW, rfl⟩
  have hq := hWs hqW
  refine ⟨W ∩ F.dom Ψ Ψ' (F.map Ψ Ψ' h q), hW.inter (F.isOpen_dom _ _ _), ⟨?_, ?_⟩,
    inter_subset_right, ?_⟩
  · rw [F.src_map Ψ Ψ' h q hq]
    exact hqW
  · have := F.mem_dom Ψ Ψ' (F.map Ψ Ψ' h q)
    rwa [F.src_map Ψ Ψ' h q hq] at this ⊢
  · rintro _ ⟨p, ⟨hpW, hpd⟩, rfl⟩
    exact ⟨p, hpW, (F.stability Ψ Ψ' h q hq p ⟨hpd, hWs hpW⟩).symm⟩

/-- The source map `s : M(Ψ, Ψ') → O` is continuous. -/
theorem continuous_src : Continuous fun a : F.Tr Ψ Ψ' => (a : Ψ.1.Trans Ψ'.1).src := by
  refine continuous_def.2 fun N hN h hh => ⟨N ∩ F.dom Ψ Ψ' h, hN.inter (F.isOpen_dom _ _ _),
    ⟨hh, F.mem_dom _ _ _⟩, inter_subset_right, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  change (F.map Ψ Ψ' h p).src ∈ N
  rw [F.src_map Ψ Ψ' h p hp.2]
  exact hp.1

/-- **2021 Proposition 19.3.4 (2), p. 874**: `F_h` is continuous at every point of `V(o)`. -/
theorem continuousAt_map (h : Ψ.1.Trans Ψ'.1) {q : Ψ.1.O} (hq : q ∈ F.dom Ψ Ψ' h) :
    ContinuousAt (fun p => F.toTr (F.map Ψ Ψ' h p)) q := by
  rw [continuousAt_def]
  intro A hA
  obtain ⟨P, hPA, hPo, hkP⟩ := mem_nhds_iff.1 hA
  obtain ⟨V, hV, hoV, -, hVP⟩ := hPo _ hkP
  rw [F.src_map Ψ Ψ' h q hq] at hoV
  have hqd : q ∈ F.dom Ψ Ψ' (F.map Ψ Ψ' h q) := by
    have := F.mem_dom Ψ Ψ' (F.map Ψ Ψ' h q)
    rwa [F.src_map Ψ Ψ' h q hq] at this
  refine mem_of_superset (((hV.inter (F.isOpen_dom _ _ _)).inter
    (F.isOpen_dom _ _ _)).mem_nhds ⟨⟨hoV, hqd⟩, hq⟩) fun p hp => hPA ?_
  change F.map Ψ Ψ' h p ∈ P
  rw [← F.stability Ψ Ψ' h q hq p ⟨hp.1.2, hp.2⟩]
  exact hVP ⟨p, hp.1.1, rfl⟩

theorem continuousOn_map (h : Ψ.1.Trans Ψ'.1) :
    ContinuousOn (fun p => F.toTr (F.map Ψ Ψ' h p)) (F.dom Ψ Ψ' h) :=
  fun _ hq => (F.continuousAt_map Ψ Ψ' h hq).continuousWithinAt

/-- **`F_h : V(o) → F_h(V(o))` as an open partial homeomorphism** with inverse `s` (Proposition
19.3.4 (1), (2)). -/
def sheet (h : Ψ.1.Trans Ψ'.1) : OpenPartialHomeomorph Ψ.1.O (F.Tr Ψ Ψ') where
  toFun p := F.toTr (F.map Ψ Ψ' h p)
  invFun a := (a : Ψ.1.Trans Ψ'.1).src
  source := F.dom Ψ Ψ' h
  target := F.map Ψ Ψ' h '' F.dom Ψ Ψ' h
  map_source' _ hq := mem_image_of_mem _ hq
  map_target' := by
    rintro _ ⟨q, hq, rfl⟩
    show (F.map Ψ Ψ' h q).src ∈ _
    rw [F.src_map Ψ Ψ' h q hq]
    exact hq
  left_inv' q hq := F.src_map Ψ Ψ' h q hq
  right_inv' := by
    rintro _ ⟨q, hq, rfl⟩
    change F.map Ψ Ψ' h (F.map Ψ Ψ' h q).src = F.map Ψ Ψ' h q
    rw [F.src_map Ψ Ψ' h q hq]
  open_source := F.isOpen_dom _ _ _
  open_target := F.isOpen_image_map Ψ Ψ' h (F.isOpen_dom _ _ _) subset_rfl
  continuousOn_toFun := F.continuousOn_map Ψ Ψ' h
  continuousOn_invFun := (F.continuous_src Ψ Ψ').continuousOn

theorem mem_sheet_target (h : Ψ.1.Trans Ψ'.1) : F.toTr h ∈ (F.sheet Ψ Ψ' h).target :=
  ⟨h.src, F.mem_dom _ _ _, F.map_src _ _ _⟩

/-- **2021 Proposition 19.3.4 (2), p. 874**: `F_h : V(o) → F_h(V(o))` is a homeomorphism onto an
open subset. -/
theorem isOpenEmbedding_restrict_map (h : Ψ.1.Trans Ψ'.1) :
    IsOpenEmbedding ((F.dom Ψ Ψ' h).domRestrict fun p => F.toTr (F.map Ψ Ψ' h p)) :=
  (F.sheet Ψ Ψ' h).isOpenEmbedding_restrict

/-- **2021 Proposition 19.3.4 (3), p. 874**: `T_{Ψ,Ψ'}` is Hausdorff (by (F)). -/
theorem t2Space : T2Space (F.Tr Ψ Ψ') := by
  refine ⟨fun h₁ h₂ hne => ?_⟩
  by_cases hs : (h₁ : Ψ.1.Trans Ψ'.1).src = (h₂ : Ψ.1.Trans Ψ'.1).src
  · obtain ⟨V, hV, hoV, hVs, hdisj⟩ := F.hausdorff Ψ Ψ' h₁ h₂ hne hs
    refine ⟨_, _, F.isOpen_image_map Ψ Ψ' h₁ hV fun q hq => (hVs hq).1,
      F.isOpen_image_map Ψ Ψ' h₂ hV fun q hq => (hVs hq).2, ⟨_, hoV, F.map_src _ _ _⟩,
      ⟨_, hs ▸ hoV, F.map_src _ _ _⟩, hdisj⟩
  · obtain ⟨A, B, hA, hB, hxA, hyB, hAB⟩ := t2_separation hs
    exact ⟨_, _, hA.preimage (F.continuous_src Ψ Ψ'), hB.preimage (F.continuous_src Ψ Ψ'),
      hxA, hyB, hAB.preimage _⟩

/-- **2021 Proposition 19.3.5 (1), p. 875**: `s : M(Ψ, Ψ') → O` is a local homeomorphism. -/
theorem isLocalHomeomorph_src :
    IsLocalHomeomorph fun a : F.Tr Ψ Ψ' => (a : Ψ.1.Trans Ψ'.1).src :=
  fun a => ⟨(F.sheet Ψ Ψ' a).symm, F.mem_sheet_target Ψ Ψ' a, rfl⟩

/-- **2021 Proposition 19.3.5 (4), p. 875, continuity**: `ι : M(Ψ, Ψ') → M(Ψ', Ψ)` is continuous
(by (D)). -/
theorem continuous_inv :
    Continuous fun a : F.Tr Ψ Ψ' => F.toTr (a : Ψ.1.Trans Ψ'.1).inv := by
  refine continuous_iff_continuousAt.2 fun h₀ => ?_
  obtain ⟨h, rfl⟩ : ∃ h : Ψ.1.Trans Ψ'.1, F.toTr h = h₀ := ⟨h₀, rfl⟩
  have hinv : h.tgt ∈ F.dom Ψ' Ψ h.inv := F.mem_dom Ψ' Ψ h.inv
  obtain ⟨N, hN, hoN, hNs, hNf⟩ := F.exists_nbhd_fmap Ψ Ψ' h (F.isOpen_dom _ _ _) hinv
  have hS : (F.map Ψ Ψ' h '' N : Set (F.Tr Ψ Ψ')) ∈ 𝓝 (F.toTr h) :=
    (F.isOpen_image_map Ψ Ψ' h hN hNs).mem_nhds ⟨_, hoN, F.map_src _ _ _⟩
  have heq : (fun a : F.Tr Ψ Ψ' => F.toTr (F.map Ψ' Ψ h.inv
      (F.fmap Ψ Ψ' h (a : Ψ.1.Trans Ψ'.1).src))) =ᶠ[𝓝 (F.toTr h)]
      fun a => F.toTr (a : Ψ.1.Trans Ψ'.1).inv := by
    filter_upwards [hS]
    rintro _ ⟨q, hq, rfl⟩
    change F.map Ψ' Ψ h.inv (F.fmap Ψ Ψ' h (F.map Ψ Ψ' h q).src) = (F.map Ψ Ψ' h q).inv
    rw [F.src_map Ψ Ψ' h q (hNs hq)]
    exact F.inversion Ψ Ψ' h q (hNs hq) (hNf q hq)
  refine ContinuousAt.congr ?_ heq
  have h1 : ContinuousAt (fun a : F.Tr Ψ Ψ' => (a : Ψ.1.Trans Ψ'.1).src) (F.toTr h) :=
    (F.continuous_src Ψ Ψ').continuousAt
  have h2 : ContinuousAt (F.fmap Ψ Ψ' h) h.src :=
    (F.continuousOn_fmap Ψ Ψ' h).continuousAt ((F.isOpen_dom _ _ _).mem_nhds (F.mem_dom _ _ _))
  have h3 : ContinuousAt (fun p => F.toTr (F.map Ψ' Ψ h.inv p)) (F.fmap Ψ Ψ' h h.src) := by
    rw [F.fmap_src]
    exact F.continuousAt_map Ψ' Ψ _ hinv
  exact ContinuousAt.comp_of_eq h3 (h2.comp_of_eq h1 rfl) rfl

/-- **2021 Proposition 19.3.5 (4), p. 875**: `ι : M(Ψ, Ψ') → M(Ψ', Ψ)` is a homeomorphism. -/
def invHomeomorph : F.Tr Ψ Ψ' ≃ₜ F.Tr Ψ' Ψ where
  toFun a := F.toTr (a : Ψ.1.Trans Ψ'.1).inv
  invFun a := F.toTr (a : Ψ'.1.Trans Ψ.1).inv
  left_inv a := inv_inv (a : Ψ.1.Trans Ψ'.1)
  right_inv a := inv_inv (a : Ψ'.1.Trans Ψ.1)
  continuous_toFun := F.continuous_inv Ψ Ψ'
  continuous_invFun := F.continuous_inv Ψ' Ψ

/-- **2021 Proposition 19.3.5 (2), p. 875**: `t : M(Ψ, Ψ') → O'` is a local homeomorphism
(`t = s ∘ ι`). -/
theorem isLocalHomeomorph_tgt :
    IsLocalHomeomorph fun a : F.Tr Ψ Ψ' => (a : Ψ.1.Trans Ψ'.1).tgt :=
  (F.isLocalHomeomorph_src Ψ' Ψ).comp (F.invHomeomorph Ψ Ψ').isLocalHomeomorph

/-- **2021 Proposition 19.3.5 (3), p. 875**: `u : O → M(Ψ, Ψ)` is continuous (by (C)). -/
theorem continuous_unit :
    Continuous fun o : Ψ.1.O => F.toTr (TransitionSet.unit o : Ψ.1.Trans Ψ.1) := by
  refine continuous_iff_continuousAt.2 fun o => ?_
  have ho : o ∈ F.dom Ψ Ψ (TransitionSet.unit o : Ψ.1.Trans Ψ.1) :=
    F.mem_dom Ψ Ψ (TransitionSet.unit o : Ψ.1.Trans Ψ.1)
  refine (F.continuousAt_map Ψ Ψ _ ho).congr ?_
  filter_upwards [(F.isOpen_dom _ _ _).mem_nhds ho] with q hq
  exact F.identity Ψ o q hq

/-- The source of `M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ')`: pairs `(h', h)` with `s(h') = t(h)`, with the
subspace topology of the product (Chapter 17's `MPolyfold.fibredProduct src tgt`). -/
abbrev FibProd (Ψ Ψ' Ψ'' : U.Unif) : Type u :=
  {p : F.Tr Ψ' Ψ'' × F.Tr Ψ Ψ' // (p.1 : Ψ'.1.Trans Ψ''.1).src = (p.2 : Ψ.1.Trans Ψ'.1).tgt}

/-- **The multiplication map** `m : M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ') → M(Ψ, Ψ'')`,
`m((o', φ', o''), (o, φ, o')) = (o, φ' ∘ φ, o'')` (Chapter 17's `TransitionSet.mul`). -/
def mulMap (Ψ Ψ' Ψ'' : U.Unif) (p : F.FibProd Ψ Ψ' Ψ'') : F.Tr Ψ Ψ'' :=
  TransitionSet.comp (p.1.1 : Ψ'.1.Trans Ψ''.1) (p.1.2 : Ψ.1.Trans Ψ'.1)
    (GroupoidStr.TransitionSet.mor_composable_of_src_eq_tgt p.2)

end Sheets

section Mul

variable {Ψ Ψ' Ψ'' : U.Unif}

/-- The neighbourhood `N = V(m(h', h)) ∩ V(o) ∩ f_h⁻¹(V(o'))` of `o` used in Proposition 19.3.5 (5)
and Remark 19.3.6 (b). -/
def mulNbhdDom (h : Ψ.1.Trans Ψ'.1) (h' : Ψ'.1.Trans Ψ''.1) (hh : h'.src = h.tgt) :
    Set Ψ.1.O :=
  F.dom Ψ Ψ'' (TransitionSet.comp h' h
      (GroupoidStr.TransitionSet.mor_composable_of_src_eq_tgt hh)) ∩
    (F.dom Ψ Ψ' h ∩ F.fmap Ψ Ψ' h ⁻¹' F.dom Ψ' Ψ'' h')

theorem isOpen_mulNbhdDom (h : Ψ.1.Trans Ψ'.1) (h' : Ψ'.1.Trans Ψ''.1) (hh : h'.src = h.tgt) :
    IsOpen (F.mulNbhdDom h h' hh) :=
  (F.isOpen_dom _ _ _).inter ((F.continuousOn_fmap Ψ Ψ' h).isOpen_inter_preimage
    (F.isOpen_dom _ _ _) (F.isOpen_dom _ _ _))

theorem src_mem_mulNbhdDom (h : Ψ.1.Trans Ψ'.1) (h' : Ψ'.1.Trans Ψ''.1) (hh : h'.src = h.tgt) :
    h.src ∈ F.mulNbhdDom h h' hh := by
  refine ⟨F.mem_dom Ψ Ψ'' _, F.mem_dom _ _ _, ?_⟩
  rw [mem_preimage, F.fmap_src, ← hh]
  exact F.mem_dom _ _ _

/-- The neighbourhood `{(k', k) | k ∈ F_h(N), k' ∈ F_{h'}(V(o'))}` of `(h', h)`. -/
def mulNbhd (h : Ψ.1.Trans Ψ'.1) (h' : Ψ'.1.Trans Ψ''.1) (hh : h'.src = h.tgt) :
    Set (F.FibProd Ψ Ψ' Ψ'') :=
  {p | (p.1.1 : Ψ'.1.Trans Ψ''.1) ∈ F.map Ψ' Ψ'' h' '' F.dom Ψ' Ψ'' h' ∧
    (p.1.2 : Ψ.1.Trans Ψ'.1) ∈ F.map Ψ Ψ' h '' F.mulNbhdDom h h' hh}

theorem mulNbhd_mem_nhds (h : Ψ.1.Trans Ψ'.1) (h' : Ψ'.1.Trans Ψ''.1) (hh : h'.src = h.tgt) :
    F.mulNbhd h h' hh ∈ 𝓝 (⟨(F.toTr h', F.toTr h), hh⟩ : F.FibProd Ψ Ψ' Ψ'') := by
  refine IsOpen.mem_nhds ?_ ⟨⟨_, F.mem_dom _ _ _, F.map_src _ _ _⟩,
    ⟨_, F.src_mem_mulNbhdDom h h' hh, F.map_src _ _ _⟩⟩
  exact ((F.isOpen_image_map Ψ' Ψ'' h' (F.isOpen_dom _ _ _) subset_rfl).preimage
    (continuous_fst.comp continuous_subtype_val)).inter
    ((F.isOpen_image_map Ψ Ψ' h (F.isOpen_mulNbhdDom h h' hh)
      fun _ hq => hq.2.1).preimage (continuous_snd.comp continuous_subtype_val))

/-- A point `(k', k)` of `mulNbhd` is `(F_{h'}(f_h(q)), F_h(q))` for `q = s(k) ∈ N`. -/
theorem mulNbhd_spec (h : Ψ.1.Trans Ψ'.1) (h' : Ψ'.1.Trans Ψ''.1) (hh : h'.src = h.tgt)
    {p : F.FibProd Ψ Ψ' Ψ''} (hp : p ∈ F.mulNbhd h h' hh) :
    (p.1.2 : Ψ.1.Trans Ψ'.1).src ∈ F.mulNbhdDom h h' hh ∧
      (p.1.2 : Ψ.1.Trans Ψ'.1) = F.map Ψ Ψ' h (p.1.2 : Ψ.1.Trans Ψ'.1).src ∧
      (p.1.1 : Ψ'.1.Trans Ψ''.1) =
        F.map Ψ' Ψ'' h' (F.fmap Ψ Ψ' h (p.1.2 : Ψ.1.Trans Ψ'.1).src) := by
  obtain ⟨⟨v, hv, hk'⟩, ⟨u, hu, hk⟩⟩ := hp
  have hsrc : (p.1.2 : Ψ.1.Trans Ψ'.1).src = u := by
    rw [← hk]
    exact F.src_map Ψ Ψ' h u hu.2.1
  refine ⟨hsrc ▸ hu, by rw [hsrc, hk], ?_⟩
  have hv' : v = F.fmap Ψ Ψ' h (p.1.2 : Ψ.1.Trans Ψ'.1).src := by
    have e := p.2
    rw [← hk', F.src_map Ψ' Ψ'' h' v hv] at e
    rw [e, hsrc, fmap, ← hk]
  rw [← hk', hv']

/-- On `mulNbhd`, `m(k', k) = F_{m(h', h)}(s(k))` (by (E)). -/
theorem mulMap_eq_of_mem (h : Ψ.1.Trans Ψ'.1) (h' : Ψ'.1.Trans Ψ''.1) (hh : h'.src = h.tgt)
    {p : F.FibProd Ψ Ψ' Ψ''} (hp : p ∈ F.mulNbhd h h' hh) :
    F.mulMap Ψ Ψ' Ψ'' p = F.map Ψ Ψ'' (TransitionSet.comp h' h
      (GroupoidStr.TransitionSet.mor_composable_of_src_eq_tgt hh))
        (p.1.2 : Ψ.1.Trans Ψ'.1).src := by
  obtain ⟨hu, h2, h1⟩ := F.mulNbhd_spec h h' hh hp
  exact (comp_congr h1 h2 _ (GroupoidStr.TransitionSet.mor_composable_of_src_eq_tgt
    (F.src_map Ψ' Ψ'' h' _ hu.2.2))).trans
    (F.multiplication Ψ Ψ' Ψ'' h h' hh _ hu.2.1 hu.2.2 hu.1)

/-- **2021 Proposition 19.3.5 (5), p. 875**: the multiplication map is continuous (by (E)). -/
theorem continuous_mulMap : Continuous (F.mulMap Ψ Ψ' Ψ'') := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  obtain ⟨⟨h', h⟩, hh⟩ := p
  have hev : (fun p : F.FibProd Ψ Ψ' Ψ'' => F.toTr (F.map Ψ Ψ'' (TransitionSet.comp
      (h' : Ψ'.1.Trans Ψ''.1) (h : Ψ.1.Trans Ψ'.1)
      (GroupoidStr.TransitionSet.mor_composable_of_src_eq_tgt hh))
        (p.1.2 : Ψ.1.Trans Ψ'.1).src)) =ᶠ[𝓝 (⟨(h', h), hh⟩ : F.FibProd Ψ Ψ' Ψ'')]
      F.mulMap Ψ Ψ' Ψ'' := by
    filter_upwards [F.mulNbhd_mem_nhds (Ψ'' := Ψ'') h h' hh] with q hq
    exact (F.mulMap_eq_of_mem h h' hh hq).symm
  refine ContinuousAt.congr ?_ hev
  have hc : Continuous fun p : F.FibProd Ψ Ψ' Ψ'' => (p.1.2 : Ψ.1.Trans Ψ'.1).src :=
    (F.continuous_src Ψ Ψ').comp (continuous_snd.comp continuous_subtype_val)
  exact ContinuousAt.comp_of_eq (F.continuousAt_map Ψ Ψ'' _ (F.mem_dom Ψ Ψ'' (TransitionSet.comp
    (h' : Ψ'.1.Trans Ψ''.1) (h : Ψ.1.Trans Ψ'.1)
    (GroupoidStr.TransitionSet.mor_composable_of_src_eq_tgt hh)))) hc.continuousAt rfl

/-- The inverse of `m` on `mulNbhd`: `q ↦ (F_{h'}(f_h(q)), F_h(q))` on `N`. -/
def mulNbhdInv (h : Ψ.1.Trans Ψ'.1) (h' : Ψ'.1.Trans Ψ''.1) (hh : h'.src = h.tgt)
    (q : F.mulNbhdDom h h' hh) : F.mulNbhd h h' hh :=
  ⟨⟨(F.toTr (F.map Ψ' Ψ'' h' (F.fmap Ψ Ψ' h q)), F.toTr (F.map Ψ Ψ' h q)),
    F.src_map Ψ' Ψ'' h' _ q.2.2.2⟩, ⟨_, q.2.2.2, rfl⟩, ⟨_, q.2, rfl⟩⟩

/-- `mulNbhd ≃ₜ N`, `(k', k) ↦ s(k)`. -/
def mulNbhdHomeomorph (h : Ψ.1.Trans Ψ'.1) (h' : Ψ'.1.Trans Ψ''.1) (hh : h'.src = h.tgt) :
    F.mulNbhd h h' hh ≃ₜ F.mulNbhdDom h h' hh where
  toFun p := ⟨(p.1.1.2 : Ψ.1.Trans Ψ'.1).src, (F.mulNbhd_spec h h' hh p.2).1⟩
  invFun := F.mulNbhdInv h h' hh
  left_inv p := by
    obtain ⟨-, h2, h1⟩ := F.mulNbhd_spec h h' hh p.2
    exact Subtype.ext (Subtype.ext (Prod.ext h1.symm h2.symm))
  right_inv q := Subtype.ext (F.src_map Ψ Ψ' h q q.2.2.1)
  continuous_toFun := ((F.continuous_src Ψ Ψ').comp (continuous_snd.comp
    (continuous_subtype_val.comp continuous_subtype_val))).subtype_mk _
  continuous_invFun := by
    have hf : Continuous fun q : F.mulNbhdDom h h' hh => F.fmap Ψ Ψ' h q :=
      (F.continuousOn_fmap Ψ Ψ' h).comp_continuous continuous_subtype_val fun q => q.2.2.1
    refine Continuous.subtype_mk (Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _) _
    · exact (F.continuousOn_map Ψ' Ψ'' h').comp_continuous hf fun q => q.2.2.2
    · exact (F.continuousOn_map Ψ Ψ' h).comp_continuous continuous_subtype_val
        fun q => q.2.2.1

/-- **2021 Remark 19.3.6 (b), p. 876**: the multiplication map is a local homeomorphism. -/
theorem isLocalHomeomorph_mulMap : IsLocalHomeomorph (F.mulMap Ψ Ψ' Ψ'') := by
  refine isLocalHomeomorph_iff_isOpenEmbedding_restrict.2 fun p => ?_
  obtain ⟨⟨h', h⟩, hh⟩ := p
  refine ⟨_, F.mulNbhd_mem_nhds (Ψ'' := Ψ'') h h' hh, ?_⟩
  set m := TransitionSet.comp (h' : Ψ'.1.Trans Ψ''.1) (h : Ψ.1.Trans Ψ'.1)
    (GroupoidStr.TransitionSet.mor_composable_of_src_eq_tgt hh)
  have hN : F.mulNbhdDom h h' hh = (F.sheet Ψ Ψ'' m).source ∩
      (F.dom Ψ Ψ' h ∩ F.fmap Ψ Ψ' h ⁻¹' F.dom Ψ' Ψ'' h') := rfl
  have hemb : IsOpenEmbedding ((F.mulNbhdDom h h' hh).domRestrict
      fun q => F.toTr (F.map Ψ Ψ'' m q)) := by
    have := ((F.sheet Ψ Ψ'' m).restrOpen _ ((F.continuousOn_fmap Ψ Ψ' h).isOpen_inter_preimage
      (F.isOpen_dom _ _ _) (F.isOpen_dom Ψ' Ψ'' h'))).isOpenEmbedding_restrict
    rwa [OpenPartialHomeomorph.restrOpen_source, ← hN] at this
  have heq : (F.mulNbhd h h' hh).domRestrict (F.mulMap Ψ Ψ' Ψ'') =
      (F.mulNbhdDom h h' hh).domRestrict (fun q => F.toTr (F.map Ψ Ψ'' m q)) ∘
        F.mulNbhdHomeomorph h h' hh := by
    funext p
    exact F.mulMap_eq_of_mem h h' hh p.2
  rw [heq]
  exact hemb.comp (F.mulNbhdHomeomorph h h' hh).isOpenEmbedding

end Mul

section Unit

variable (Ψ : U.Unif)

/-- **2021 Remark 19.3.6 (a), p. 875**: `u : O → M(Ψ, Ψ)` is a homeomorphism onto an open
subset. -/
theorem isOpenEmbedding_unit :
    IsOpenEmbedding fun o : Ψ.1.O => F.toTr (TransitionSet.unit o : Ψ.1.Trans Ψ.1) := by
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap (F.continuous_unit Ψ)
    (fun o o' h => congrArg (fun a : Ψ.1.Trans Ψ.1 => a.src) h) fun A hA => ?_
  refine isOpen_iff_forall_mem_open.2 ?_
  rintro _ ⟨o, hoA, rfl⟩
  have ho : o ∈ F.dom Ψ Ψ (TransitionSet.unit o : Ψ.1.Trans Ψ.1) :=
    F.mem_dom Ψ Ψ (TransitionSet.unit o : Ψ.1.Trans Ψ.1)
  refine ⟨F.map Ψ Ψ (TransitionSet.unit o) '' (A ∩ F.dom Ψ Ψ (TransitionSet.unit o)), ?_,
    F.isOpen_image_map Ψ Ψ _ (hA.inter (F.isOpen_dom _ _ _)) inter_subset_right,
    ⟨o, ⟨hoA, ho⟩, F.map_src Ψ Ψ (TransitionSet.unit o : Ψ.1.Trans Ψ.1)⟩⟩
  rintro _ ⟨q, hq, rfl⟩
  exact ⟨q, hq.1, (F.identity Ψ o q hq.2).symm⟩

/-- **2021 Proposition 19.3.7, p. 877**: `Ψ̄ : G × O → M(Ψ, Ψ)`, `(g, o) ↦ (o, Ψ(g, o), g ∗ o)`,
is a homeomorphism (continuity from the special form of (A)). -/
def hatHomeomorph : Ψ.1.G × Ψ.1.O ≃ₜ F.Tr Ψ Ψ where
  toFun x := F.toTr (Ψ.1.hat x)
  invFun := Ψ.1.hatEquiv.symm
  left_inv := Ψ.1.hatEquiv.symm_apply_apply
  right_inv := Ψ.1.hatEquiv.apply_symm_apply
  continuous_toFun := by
    refine continuous_iff_continuousAt.2 fun p => ?_
    have hp : p.2 ∈ F.dom Ψ Ψ (Ψ.1.hat p) := F.mem_dom Ψ Ψ (Ψ.1.hat p)
    have hnhds : ({p.1} ×ˢ F.dom Ψ Ψ (Ψ.1.hat p) : Set (Ψ.1.G × Ψ.1.O)) ∈ 𝓝 p :=
      ((isOpen_discrete _).prod (F.isOpen_dom _ _ _)).mem_nhds ⟨rfl, hp⟩
    refine ((F.continuousAt_map Ψ Ψ _ hp).comp continuousAt_snd).congr ?_
    filter_upwards [hnhds] with x hx
    obtain ⟨g, q⟩ := x
    obtain ⟨hg, hq⟩ := hx
    change g = p.1 at hg
    subst hg
    exact F.map_hat Ψ p q hq
  continuous_invFun := by
    refine continuous_iff_continuousAt.2 fun a => ?_
    obtain ⟨p, rfl⟩ := Ψ.1.hat_bijective.2 a
    have hS : (F.map Ψ Ψ (Ψ.1.hat p) '' F.dom Ψ Ψ (Ψ.1.hat p) : Set (F.Tr Ψ Ψ)) ∈
        𝓝 (F.toTr (Ψ.1.hat p)) :=
      (F.isOpen_image_map Ψ Ψ _ (F.isOpen_dom _ _ _) subset_rfl).mem_nhds
        (F.mem_sheet_target Ψ Ψ _)
    refine (continuousAt_const (y := p.1).prodMk (F.continuous_src Ψ Ψ).continuousAt).congr ?_
    filter_upwards [hS]
    rintro _ ⟨q, hq, rfl⟩
    show (p.1, (F.map Ψ Ψ (Ψ.1.hat p) q).src) = Ψ.1.hatEquiv.symm (F.map Ψ Ψ (Ψ.1.hat p) q)
    rw [F.map_hat Ψ p q hq]
    exact (Ψ.1.hatEquiv.symm_apply_apply (p.1, q)).symm

theorem hatHomeomorph_apply (x : Ψ.1.G × Ψ.1.O) : F.hatHomeomorph Ψ x = Ψ.1.hat x := rfl

end Unit

/-- **2021 Lemma 19.3.8, p. 878**: `T_{Ψ,Ψ'}` is regular (`s` is a local homeomorphism into the
regular space `O`, and `T_{Ψ,Ψ'}` is Hausdorff). -/
theorem regularSpace (Ψ Ψ' : U.Unif) : RegularSpace (F.Tr Ψ Ψ') := by
  have := F.t2Space Ψ Ψ'
  exact Chapter19.regularSpace_of_isLocalHomeomorph_of_t2 (F.isLocalHomeomorph_src Ψ Ψ')

/-- `T_{Ψ,Ψ'}` is locally metrizable (`s` is a local homeomorphism into the metrizable `O`). -/
theorem exists_isOpen_metrizableSpace (Ψ Ψ' : U.Unif) (h : F.Tr Ψ Ψ') :
    ∃ W : Set (F.Tr Ψ Ψ'), IsOpen W ∧ h ∈ W ∧ MetrizableSpace W := by
  have := Ψ.1.P.metrizableSpace
  exact Chapter19.exists_isOpen_metrizableSpace_of_isLocalHomeomorph
    (F.isLocalHomeomorph_src Ψ Ψ') h

end TransitionData

/-- **2021 Definition 19.3.2, p. 873**: the topology `T_{Ψ,Ψ'}` of a transition construction: the
`T^F_{Ψ,Ψ'}` of any representative `F` (well defined by Lemma 19.3.1). -/
abbrev TransitionConstruction.topology {U : C.UniformizerConstruction}
    (𝓕 : U.TransitionConstruction)
    (Ψ Ψ' : U.Unif) : TopologicalSpace (Ψ.1.Trans Ψ'.1) :=
  Quotient.lift (fun F : U.TransitionData => F.topology Ψ Ψ')
    (fun _ _ e => TopologicalSpace.ext (TransitionData.lemma_19_3_1 e Ψ Ψ')) 𝓕

end UniformizerConstruction

namespace BasicConstruction

open GroupoidStr (TransitionSet)

variable (B : C.BasicConstruction)

/-- `M(Ψ, Ψ')` with its natural topology `T_{Ψ,Ψ'}` (Definition 19.3.2), carried by the
representative `B.rep` (`definition_19_3_2`). -/
abbrev M (Ψ Ψ' : B.U.Unif) : Type u := B.rep.Tr Ψ Ψ'

/-- **2021 Definition 19.3.2, p. 873**: `T_{Ψ,Ψ'}` is the topology `T^F_{Ψ,Ψ'}` of every
representative `F` of `𝓕`; it is the topology of `B.M Ψ Ψ'`. -/
theorem definition_19_3_2 {F : B.U.TransitionData} (hF : (⟦F⟧ : B.U.TransitionConstruction) = B.𝓕)
    (Ψ Ψ' : B.U.Unif) :
    B.𝓕.topology Ψ Ψ' = F.topology Ψ Ψ' ∧
      (inferInstance : TopologicalSpace (B.M Ψ Ψ')) = B.𝓕.topology Ψ Ψ' := by
  have h1 : ∀ F' : B.U.TransitionData, (⟦F'⟧ : B.U.TransitionConstruction) = B.𝓕 →
      B.𝓕.topology Ψ Ψ' = F'.topology Ψ Ψ' := by
    intro F' hF'
    rw [← hF']
    rfl
  exact ⟨h1 F hF, (h1 B.rep B.mk_rep).symm⟩

theorem isOpen_M_iff {F : B.U.TransitionData} (hF : (⟦F⟧ : B.U.TransitionConstruction) = B.𝓕)
    {Ψ Ψ' : B.U.Unif} {W : Set (B.M Ψ Ψ')} : IsOpen W ↔ F.IsOpenTr Ψ Ψ' W := by
  have e : B.rep.Equiv F := Quotient.exact (B.mk_rep.trans hF.symm)
  rw [B.rep.isOpen_tr_iff, UniformizerConstruction.TransitionData.lemma_19_3_1 e]

/-- The identity `M(Ψ, Ψ') → M(Ψ, Ψ')` from `T^F_{Ψ,Ψ'}` (any representative) to `T_{Ψ,Ψ'}`. -/
def trHomeomorph {F : B.U.TransitionData} (hF : (⟦F⟧ : B.U.TransitionConstruction) = B.𝓕)
    (Ψ Ψ' : B.U.Unif) : F.Tr Ψ Ψ' ≃ₜ B.M Ψ Ψ' where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_def.2 fun _ hW => (B.isOpen_M_iff hF).1 hW
  continuous_invFun := continuous_def.2 fun _ hW => (B.isOpen_M_iff hF).2 hW

/-- **2021 Proposition 19.3.4, p. 874**: for a representative `F` of `𝓕` and
`h = (o, φ, o') ∈ M(Ψ, Ψ')`: (1) `F_h(W)` is open for every open `W ⊂ V(o)`; (2) `F_h` is
continuous on `V(o)` and a homeomorphism onto the open set `F_h(V(o))`; (3) `T_{Ψ,Ψ'}` is
Hausdorff.  (That `T_{Ψ,Ψ'}` is a topology: `TransitionData.isOpenTr_topology`.) -/
theorem proposition_19_3_4 {F : B.U.TransitionData}
    (hF : (⟦F⟧ : B.U.TransitionConstruction) = B.𝓕) (Ψ Ψ' : B.U.Unif) :
    (∀ (h : Ψ.1.Trans Ψ'.1) (W : Set Ψ.1.O), IsOpen W → W ⊆ F.dom Ψ Ψ' h →
        IsOpen (X := B.M Ψ Ψ') (F.map Ψ Ψ' h '' W)) ∧
      (∀ h : Ψ.1.Trans Ψ'.1,
        ContinuousOn (fun q => B.rep.toTr (F.map Ψ Ψ' h q)) (F.dom Ψ Ψ' h) ∧
        IsOpenEmbedding ((F.dom Ψ Ψ' h).domRestrict fun q => B.rep.toTr (F.map Ψ Ψ' h q))) ∧
      T2Space (B.M Ψ Ψ') :=
  ⟨fun h _ hW hWs => (B.isOpen_M_iff hF).2 (F.isOpen_image_map Ψ Ψ' h hW hWs),
    fun h => ⟨(B.trHomeomorph hF Ψ Ψ').continuous.comp_continuousOn (F.continuousOn_map Ψ Ψ' h),
      (B.trHomeomorph hF Ψ Ψ').isOpenEmbedding.comp (F.isOpenEmbedding_restrict_map Ψ Ψ' h)⟩,
    B.rep.t2Space Ψ Ψ'⟩

/-- **2021 Proposition 19.3.4, p. 874, first assertion**: `T_{Ψ,Ψ'}` is a topology (for a
representative `F`, the collection `T^F_{Ψ,Ψ'}` has the axioms of a topology). -/
theorem proposition_19_3_4_topology (F : B.U.TransitionData) (Ψ Ψ' : B.U.Unif) :
    F.IsOpenTr Ψ Ψ' univ ∧
      (∀ W₁ W₂, F.IsOpenTr Ψ Ψ' W₁ → F.IsOpenTr Ψ Ψ' W₂ → F.IsOpenTr Ψ Ψ' (W₁ ∩ W₂)) ∧
      ∀ S : Set (Set (Ψ.1.Trans Ψ'.1)), (∀ W ∈ S, F.IsOpenTr Ψ Ψ' W) → F.IsOpenTr Ψ Ψ' (⋃₀ S) :=
  F.isOpenTr_topology Ψ Ψ'

/-- **2021 Proposition 19.3.5, p. 875**: (1) `s` and (2) `t` are local homeomorphisms, (3) `u` is
continuous, (4) `ι` is a homeomorphism, (5) `m` is continuous. -/
theorem proposition_19_3_5 (Ψ Ψ' Ψ'' : B.U.Unif) :
    IsLocalHomeomorph (fun a : B.M Ψ Ψ' => (a : Ψ.1.Trans Ψ'.1).src) ∧
      IsLocalHomeomorph (fun a : B.M Ψ Ψ' => (a : Ψ.1.Trans Ψ'.1).tgt) ∧
      Continuous (fun o : Ψ.1.O => B.rep.toTr (TransitionSet.unit o : Ψ.1.Trans Ψ.1)) ∧
      (∃ e : B.M Ψ Ψ' ≃ₜ B.M Ψ' Ψ, ∀ a, e a = (a : Ψ.1.Trans Ψ'.1).inv) ∧
      Continuous (B.rep.mulMap Ψ Ψ' Ψ'') :=
  ⟨B.rep.isLocalHomeomorph_src Ψ Ψ', B.rep.isLocalHomeomorph_tgt Ψ Ψ', B.rep.continuous_unit Ψ,
    ⟨B.rep.invHomeomorph Ψ Ψ', fun _ => rfl⟩, B.rep.continuous_mulMap⟩

/-- **2021 Remark 19.3.6 (a), p. 875**: `u : O → M(Ψ, Ψ)` is a homeomorphism onto an open
subset. -/
theorem remark_19_3_6_a (Ψ : B.U.Unif) :
    IsOpenEmbedding fun o : Ψ.1.O => B.rep.toTr (TransitionSet.unit o : Ψ.1.Trans Ψ.1) :=
  B.rep.isOpenEmbedding_unit Ψ

/-- **2021 Remark 19.3.6 (b), p. 876**: `m : M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ') → M(Ψ, Ψ'')` is a local
homeomorphism. -/
theorem remark_19_3_6_b (Ψ Ψ' Ψ'' : B.U.Unif) : IsLocalHomeomorph (B.rep.mulMap Ψ Ψ' Ψ'') :=
  B.rep.isLocalHomeomorph_mulMap

/-- **2021 Proposition 19.3.7, p. 877**: `Ψ̄ : G × O → M(Ψ, Ψ)` is a homeomorphism. -/
theorem proposition_19_3_7 (Ψ : B.U.Unif) :
    ∃ e : Ψ.1.G × Ψ.1.O ≃ₜ B.M Ψ Ψ, ∀ x, e x = Ψ.1.hat x :=
  ⟨B.rep.hatHomeomorph Ψ, fun _ => rfl⟩

/-- **2021 Lemma 19.3.8, p. 878**: `T_{Ψ,Ψ'}` is regular. -/
theorem lemma_19_3_8 (Ψ Ψ' : B.U.Unif) : RegularSpace (B.M Ψ Ψ') := B.rep.regularSpace Ψ Ψ'

/-- **2021 Theorem 19.3.3, p. 873**: `T_{Ψ,Ψ'}` is a regular, Hausdorff, locally metrizable
topology on `M(Ψ, Ψ')`, and (1) `s`, (2) `t` are local homeomorphisms, (3) `u` is continuous,
(4) `ι` is a homeomorphism, (5) `m` is continuous, (6) `Ψ̄ : G × O → M(Ψ, Ψ)` is a
homeomorphism. -/
theorem theorem_19_3_3 (Ψ Ψ' Ψ'' : B.U.Unif) :
    RegularSpace (B.M Ψ Ψ') ∧ T2Space (B.M Ψ Ψ') ∧
      (∀ h : B.M Ψ Ψ', ∃ W : Set (B.M Ψ Ψ'), IsOpen W ∧ h ∈ W ∧ MetrizableSpace W) ∧
      IsLocalHomeomorph (fun a : B.M Ψ Ψ' => (a : Ψ.1.Trans Ψ'.1).src) ∧
      IsLocalHomeomorph (fun a : B.M Ψ Ψ' => (a : Ψ.1.Trans Ψ'.1).tgt) ∧
      Continuous (fun o : Ψ.1.O => B.rep.toTr (TransitionSet.unit o : Ψ.1.Trans Ψ.1)) ∧
      (∃ e : B.M Ψ Ψ' ≃ₜ B.M Ψ' Ψ, ∀ a, e a = (a : Ψ.1.Trans Ψ'.1).inv) ∧
      Continuous (B.rep.mulMap Ψ Ψ' Ψ'') ∧
      ∃ e : Ψ.1.G × Ψ.1.O ≃ₜ B.M Ψ Ψ, ∀ x, e x = Ψ.1.hat x :=
  let ⟨h1, h2, h3, h4, h5⟩ := B.proposition_19_3_5 Ψ Ψ' Ψ''
  ⟨B.lemma_19_3_8 Ψ Ψ', B.rep.t2Space Ψ Ψ', B.rep.exists_isOpen_metrizableSpace Ψ Ψ',
    h1, h2, h3, h4, h5, B.proposition_19_3_7 Ψ⟩

end BasicConstruction

end GroupoidalCategory

end Polyfold
