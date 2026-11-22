import Polyfold.Chapter19.PolyfoldStructure
import Polyfold.Chapter17.ModelPropertiesExamples

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 19,
§19.5 (p. 888): **Theorem 19.5.3** (properness and second countability or paracompactness make
`T` metrizable, so `(S, T)` is a GCT; a metrizable `T` carries the natural polyfold structure
`(F, M)` of Definition 17.1.8, tame for tame domains).  Numbers and pages are the 2021 text's.
(The regularity conditions 19.5.5–19.5.11 are in `BasicRegularity`.)

# The polyfold structure `(F, M)` of a basic construction

## The text, paraphrased

(Theorem 19.5.3) For a basic construction `(F, 𝓕)` with natural topology `T`: (1) if `T`
satisfies the properness condition and is second countable or paracompact, `T` is metrizable,
so `(S, T)` is a GCT; (2) if `T` is metrizable there is a natural polyfold structure `(F, M)`
for `(S, T)`, tame if the domains `O` of the uniformizers of `F` are tame.

## What is formalized (namespace `Polyfold.GroupoidalCategory.BasicConstruction`)

* `toGCTOfMetrizable hB hm`: the GCT `(S, T)` (Definition 17.1.1) for metrizable `T`;
  **`theorem_19_5_3_one`**.
* `toLocalUniformizer hm hΨ`: every `Ψ ∈ F(α)` is a local uniformizer of `(S, T)` (Definition
  17.1.3; `|Ψ|` is an open embedding by Theorem 19.2.2 (3)); `gctF hm` (the uniformizer
  construction `F` of `(S, T)`, Definition 17.1.6), `toUnif hm` (its uniformizers as those of
  `F`).
* **`toPolyfoldConstruction hm`**: the polyfold structure `(F, M)` of Definition 17.1.8, with
  `M(Ψ, Ψ')` carrying the natural topology `T_{Ψ,Ψ'}` and the M-polyfold structure of Theorem
  19.5.1; (a)–(c) are Theorem 19.5.1 and Corollary 19.5.2.
* **`theorem_19_5_3_two`**: `(F, M)` is a polyfold structure for `(S, T)` whose uniformizers are
  exactly those of `F`, whose footprints cover `|S|`, whose maps `Ψ̂ : G ⋉ O → M(Ψ, Ψ)` are
  sc-diffeomorphisms (Lemma 17.1.9), and which is tame — with every `M(Ψ, Ψ')` and every model
  `X_Ψ` of Theorem 17.1.14 tame — when the domains of the uniformizers of `F` are tame.
* `isEquivalence_modelFunctor`: for every covering family, the model `X_Ψ` is equivalent to `S`
  (Lemma 17.1.15), and `isGeneralizedIso_comparison`: the comparison maps `f_{Ψ,Ψ'}` of Theorem
  17.1.18 are generalized isomorphisms.

## Readings

* "There is an underlying natural polyfold structure `(F, M)`": the uniformizer construction is
  `F` itself, each `Ψ ∈ F(α)` regarded as a local uniformizer of `(S, T)` (`gctF`), and `M` is the
  structure of Theorem 19.5.1.  Theorem 19.2.2 (3) needs every class of `|S|` to meet an object
  with `F(α) ≠ ∅` (`HasClassUniformizers`, as in Chapter 19's Theorem 19.2.2).
* "Tame": Definition 17.1.8's tameness (all domains `O` tame); we also prove that every
  `M(Ψ, Ψ')` and every model `X_Ψ` is then tame.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology TopologicalSpace

noncomputable section

namespace Polyfold

universe u

namespace GroupoidalCategory

variable {C : GroupoidalCategory.{u}}

namespace BasicConstruction

open GroupoidStr (TransitionSet)

variable (B : C.BasicConstruction) (hB : B.U.HasClassUniformizers)

/-- **The GCT `(S, T)`** (Definition 17.1.1) of a basic construction with metrizable natural
topology `T`. -/
def toGCTOfMetrizable (hm : @MetrizableSpace C.OrbitSpace (B.natTop hB)) : GCT.{u} where
  toGroupoidalCategory := C
  top := B.natTop hB
  metrizable := hm

/-- **2021 Theorem 19.5.3 (1), p. 888**: if `T` satisfies the properness condition and is second
countable or paracompact, `T` is metrizable, so that `(S, T)` is a GCT
(`toGCTOfMetrizable`). -/
theorem theorem_19_5_3_one (hv : B.PropernessV2 hB)
    (h : @SecondCountableTopology _ (B.natTop hB) ∨ @ParacompactSpace _ (B.natTop hB)) :
    @MetrizableSpace C.OrbitSpace (B.natTop hB) :=
  h.elim (B.theorem_19_4_6_one hB hv) (B.theorem_19_4_6_two hB hv)

variable {B hB} (hm : @MetrizableSpace C.OrbitSpace (B.natTop hB))

/-- **Every `Ψ ∈ F(α)` is a local uniformizer of `(S, T)`** (Definition 17.1.3): `|Ψ|` is a
homeomorphism onto an open subset (Theorem 19.2.2 (3)). -/
def toLocalUniformizer {α : C.Obj} {Ψ : C.Uniformizer} (hΨ : Ψ ∈ B.U.F α) :
    (B.toGCTOfMetrizable hB hm).LocalUniformizer where
  toUniformizer := Ψ
  isOpenEmbedding_orbitMap := (B.theorem_19_2_2_three hB hΨ).1

/-- **The uniformizer construction `F` of `(S, T)`** (Definition 17.1.6): `F(α)`, its members
regarded as local uniformizers. -/
def gctF : (B.toGCTOfMetrizable hB hm).UniformizerConstruction where
  F α := {Ψ' | Ψ'.toUniformizer ∈ B.U.F α}
  isAt α Ψ' h := B.U.isAt α Ψ'.toUniformizer h

theorem mem_gctF_iff {α : C.Obj} {Ψ' : (B.toGCTOfMetrizable hB hm).LocalUniformizer} :
    Ψ' ∈ (gctF hm).F α ↔ Ψ'.toUniformizer ∈ B.U.F α := Iff.rfl

theorem toLocalUniformizer_mem {α : C.Obj} {Ψ : C.Uniformizer} (hΨ : Ψ ∈ B.U.F α) :
    toLocalUniformizer hm hΨ ∈ (gctF hm).F α := hΨ

/-- A uniformizer of `gctF` as a uniformizer of `F`. -/
def toUnif (Ψ : (gctF hm).Unif) : B.U.Unif :=
  ⟨Ψ.1.toUniformizer, by obtain ⟨α, h⟩ := Ψ.2; exact ⟨α, h⟩⟩

@[simp] theorem toUnif_val (Ψ : (gctF hm).Unif) : (toUnif hm Ψ).1 = Ψ.1.toUniformizer := rfl

/-- A uniformizer of `F` as a uniformizer of `gctF`. -/
def ofUnif (Ψ : B.U.Unif) : (gctF hm).Unif :=
  ⟨toLocalUniformizer hm Ψ.2.choose_spec, Ψ.2.choose, Ψ.2.choose_spec⟩

@[simp] theorem toUnif_ofUnif (Ψ : B.U.Unif) : toUnif hm (ofUnif hm Ψ) = Ψ := rfl

/-- **2021 Theorem 19.5.3 (2), p. 888: the natural polyfold structure `(F, M)` of `(S, T)`**
(Definition 17.1.8): `M(Ψ, Ψ')` with the natural topology `T_{Ψ,Ψ'}` and the M-polyfold
structure of Theorem 19.5.1; (a) is Theorem 19.5.1, (b) and (c) are Corollary 19.5.2. -/
def toPolyfoldConstruction : (B.toGCTOfMetrizable hB hm).PolyfoldConstruction where
  toUniformizerConstruction := gctF hm
  topM Ψ Ψ' := B.rep.topology (toUnif hm Ψ) (toUnif hm Ψ')
  t2M Ψ Ψ' := B.rep.t2Space (toUnif hm Ψ) (toUnif hm Ψ')
  paraM Ψ Ψ' := UniformizerConstruction.TransitionData.instParacompactSpaceTr B.rep
    (toUnif hm Ψ) (toUnif hm Ψ')
  M Ψ Ψ' := B.transPolyfold (toUnif hm Ψ) (toUnif hm Ψ')
  isLocalScDiffeo_src Ψ Ψ' := B.rep.isLocalScDiffeo_src (toUnif hm Ψ) (toUnif hm Ψ')
  isLocalScDiffeo_tgt Ψ Ψ' := B.rep.isLocalScDiffeo_tgt (toUnif hm Ψ) (toUnif hm Ψ')
  isScSmoothMap_unit Ψ := B.rep.isScSmoothMap_unit (toUnif hm Ψ)
  isScSmoothMap_inv Ψ Ψ' := B.rep.isScSmoothMap_inv (toUnif hm Ψ) (toUnif hm Ψ')
  isScSmoothMap_mul Ψ Ψ' Ψ'' :=
    B.rep.isScSmoothMap_mul (toUnif hm Ψ) (toUnif hm Ψ') (toUnif hm Ψ'')

@[simp] theorem toPolyfoldConstruction_F (α : C.Obj) :
    (toPolyfoldConstruction hm).F α = {Ψ' | Ψ'.toUniformizer ∈ B.U.F α} := rfl

theorem toPolyfoldConstruction_M (Ψ Ψ' : (toPolyfoldConstruction hm).Unif) :
    (toPolyfoldConstruction hm).M Ψ Ψ' = B.transPolyfold (toUnif hm Ψ) (toUnif hm Ψ') := rfl

/-- The footprints of the uniformizers of `F` cover `|S|` (every class meets an object `α` with
`F(α) ≠ ∅`). -/
theorem hasCoveringUniformizers_toPolyfoldConstruction :
    (toPolyfoldConstruction hm).HasCoveringUniformizers := by
  refine eq_univ_of_forall fun z => mem_iUnion.2 ?_
  obtain ⟨α, hα, Ψ, hΨ⟩ := hB z
  refine ⟨⟨toLocalUniformizer hm hΨ, α, hΨ⟩, ?_⟩
  obtain ⟨-, hz⟩ := B.theorem_19_2_2_three hB hΨ
  rw [← hα]
  exact hz

/-- `Ψ̂ : G × O → M(Ψ, Ψ)` is continuous for the polyfold structure `(F, M)` (it is
`hatHomeomorph`). -/
theorem continuous_hat (Ψ : (toPolyfoldConstruction hm).Unif) :
    Continuous ((toPolyfoldConstruction hm).hat Ψ) :=
  (B.rep.hatHomeomorph (toUnif hm Ψ)).continuous

/-- **A covering family of `(F, M)`**: one uniformizer `Ψ_z ∈ F(α_z)` for every class `z`. -/
def coveringFamily : (toPolyfoldConstruction hm).CoveringFamily :=
  Classical.choice
    ((toPolyfoldConstruction hm).toUniformizerConstruction.exists_coveringFamily_iff.2
      (hasCoveringUniformizers_toPolyfoldConstruction hm))

/-- **2021 Theorem 19.5.3 (2), p. 888**: if `T` is metrizable, `(F, M)` (`toPolyfoldConstruction`)
is a polyfold structure for the GCT `(S, T)` (Definition 17.1.8): its uniformizers are those of
`F`, `M(Ψ, Ψ')` carries the natural topology and the structure of Theorem 19.5.1, the footprints
cover `|S|`, and `Ψ̂ : G ⋉ O → M(Ψ, Ψ)` is an sc-diffeomorphism (Lemma 17.1.9).  If the domains
`O` of the uniformizers of `F` are tame, `(F, M)` is tame, every `M(Ψ, Ψ')` is tame and every
model `X_Ψ` (Theorem 17.1.14) is tame. -/
theorem theorem_19_5_3_two :
    (∀ (α : C.Obj) (Ψ : C.Uniformizer), Ψ ∈ B.U.F α ↔
        ∃ Ψ' ∈ (toPolyfoldConstruction hm).F α, Ψ'.toUniformizer = Ψ) ∧
      (∀ Ψ Ψ' : (toPolyfoldConstruction hm).Unif,
        (toPolyfoldConstruction hm).M Ψ Ψ' = B.transPolyfold (toUnif hm Ψ) (toUnif hm Ψ')) ∧
      (toPolyfoldConstruction hm).HasCoveringUniformizers ∧
      (∀ Ψ : (toPolyfoldConstruction hm).Unif,
        (toPolyfoldConstruction hm).morPolyfold Ψ |>.IsScDiffeoOn
          ((toPolyfoldConstruction hm).transPolyfold Ψ Ψ) ((toPolyfoldConstruction hm).hat Ψ)
          ((toPolyfoldConstruction hm).hatInv Ψ) univ univ) ∧
      ((∀ Ψ : B.U.Unif, Ψ.1.P.IsTame) →
        (toPolyfoldConstruction hm).IsTame ∧
          (∀ Ψ Ψ' : (toPolyfoldConstruction hm).Unif,
            ((toPolyfoldConstruction hm).transPolyfold Ψ Ψ').IsTame) ∧
          ∀ c : (toPolyfoldConstruction hm).CoveringFamily,
            ((toPolyfoldConstruction hm).modelEP c.Ψ).X.IsTame) := by
  refine ⟨fun α Ψ => ⟨fun h => ⟨toLocalUniformizer hm h, h, rfl⟩, ?_⟩, fun _ _ => rfl,
    hasCoveringUniformizers_toPolyfoldConstruction hm,
    fun Ψ => ((toPolyfoldConstruction hm).lemma_17_1_9_of_continuous Ψ (continuous_hat hm Ψ)).1,
    fun ht => ?_⟩
  · rintro ⟨Ψ', h, rfl⟩
    exact h
  have hT : (toPolyfoldConstruction hm).IsTame := fun α Ψ' h => ht ⟨Ψ'.toUniformizer, α, h⟩
  exact ⟨hT, fun Ψ Ψ' => B.rep.isTame_transPolyfold _ _ (ht (toUnif hm Ψ)),
    fun c => (toPolyfoldConstruction hm).isTame_modelEpGroupoid c.Ψ hT⟩

/-- **The model `X_Ψ` of `(F, M)` is equivalent to `S`** (Lemma 17.1.15 for the polyfold
structure of Theorem 19.5.3 (2)): for every covering family, `Γ_Ψ : X_Ψ → S` is an equivalence
and `|Γ_Ψ|` a homeomorphism. -/
theorem isEquivalence_modelFunctor (c : (toPolyfoldConstruction hm).CoveringFamily) :
    ((toPolyfoldConstruction hm).modelFunctor c.Ψ).toFunctor.IsEquivalence ∧
      IsHomeomorph ((toPolyfoldConstruction hm).modelFunctor c.Ψ).orbitMap :=
  (toPolyfoldConstruction hm).lemma_17_1_15 c

/-- **Different covering families of `(F, M)` give equivalent models** (Theorem 17.1.18 for the
polyfold structure of Theorem 19.5.3 (2)): the comparison `X_Ψ → X_Ψ'` is a generalized
isomorphism. -/
theorem isGeneralizedIso_comparison (c c' : (toPolyfoldConstruction hm).CoveringFamily) :
    EPLocalization.EPLoc.IsGeneralizedIso ((toPolyfoldConstruction hm).comparison c c') :=
  ((toPolyfoldConstruction hm).theorem_17_1_18 c c' c').1

end BasicConstruction

end GroupoidalCategory

end Polyfold
