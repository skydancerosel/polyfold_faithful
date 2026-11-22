import Polyfold.Chapter17.ModelEpGroupoid
import Polyfold.Chapter16.PolyfoldStructure

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.1 (pp. 754–755): the functor `Γ_Ψ : X_Ψ → C` (17.10), **Lemma 17.1.15**, **Remark 17.1.16**,
**Definition 17.1.17** (weak polyfold structures) and (17.13).  Numbers and pages are the 2021
text's.

# The equivalence `Γ_Ψ : X_Ψ → C`

## The text, paraphrased

(17.10) `Γ_Ψ : X_Ψ → C` maps `q_λ ∈ O_λ` to `Ψ_λ(q_λ)` and `(q_λ, φ, q_λ')` to `φ`.
(Lemma 17.1.15, p. 754) `Γ_Ψ` is an equivalence of categories and `|Γ_Ψ| : |X_Ψ| → |C|` is a
homeomorphism.  *Proof*: essentially surjective since the footprints cover `|C|`; on morphism
sets `X(q_λ, q_λ') → C(Ψ_λ(q_λ), Ψ_λ'(q_λ'))` is trivially a bijection; so `|Γ_Ψ|` is a
bijection, and a homeomorphism since `|a| ↦ |Ψ_λ(a)|` is a homeomorphism of `|O_λ| = G_λ\O_λ`
onto an open subset of `|C|`.  (Remark 17.1.16, p. 755) Since `|C|` is metrizable so is `|X_Ψ|`;
`X_Ψ` is an ep-groupoid with paracompact orbit space; if `X_Ψ` satisfies (ZHOU), `(X_Ψ, |Γ_Ψ|)` is a
polyfold structure on `|C|` in the sense of Definition 16.1.1.  (Definition 17.1.17) A weak
polyfold structure on a paracompact space `Z` is a pair `(X, β)` of an ep-groupoid `X` and a
homeomorphism `β : |X| → Z`.  Then `|X|` is paracompact, hence metrizable, so `Z` is metrizable;
(ZHOU) is not required.  (17.13) `(X_Ψ, |Γ_Ψ|)` is a weak polyfold structure on `|C|`.

## What is formalized (namespace `Polyfold.GCT.PolyfoldConstruction`)

* `modelFunctor Ψ` (`Γ_Ψ`, (17.10)) for any family `Ψ : ι → S.Unif`; `IsCoveringFamily Ψ` (the
  footprints cover `|C|`); `modelFunctor_full`, `modelFunctor_faithful` (no hypothesis),
  `modelFunctor_essSurj` (for a covering family), `continuous_modelOrbitMap`,
  `isOpenMap_modelOrbitMap`, `isHomeomorph_modelOrbitMap`.
* **Lemma 17.1.15** (`lemma_17_1_15`, for a covering family; `lemma_17_1_15_of_isCovering` for a
  covering function), `modelOrbitHomeomorph` (`|Γ_Ψ|` as a homeomorphism).
* **Remark 17.1.16**: `metrizableSpace_modelOrbitSpace`, `hasParacompactOrbitSpace_model`,
  `modelPolyfoldStructure` (under (ZHOU), Definition 16.1.1), `remark_17_1_16`.
* **Definition 17.1.17**: `WeakPolyfoldStructure Z` (namespace `Polyfold`), with
  `hasParacompactOrbitSpace`, `metrizableSpace_orbitSpace`, `metrizableSpace` (the remarks after
  the definition), `toOrbitChart`, `PolyfoldStructure.toWeakPolyfoldStructure`.
* (17.13): `weakStructure c` (`(X_Ψ, |Γ_Ψ|)` is a weak polyfold structure on `|C|`).

## Readings

* `Γ_Ψ` is a functor of the underlying groupoids (`GroupoidFunctor`); `C` carries no
  M-polyfold structure, so "equivalence of categories" is Mathlib's `Functor.IsEquivalence` of the
  underlying functor between the Mathlib bridges `GroupoidStr.Ob`.
* The full and faithful parts hold for every family; essential surjectivity uses the covering
  condition, as in the text.
* `|C|` is metrizable (Definition 17.1.1), hence paracompact, which gives the paracompactness of
  `|C|` asked by Definition 17.1.17 for (17.13).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology CategoryTheory

noncomputable section

namespace Polyfold

open EPLocalization

universe u

/-! ### Definition 17.1.17: weak polyfold structures -/

/-- **2021 Definition 17.1.17, p. 755**: a **weak polyfold structure** on the paracompact space
`Z`: an ep-groupoid `X` and a homeomorphism `β : |X| → Z` ((ZHOU) is not asked). -/
structure WeakPolyfoldStructure (Z : Type u) [TopologicalSpace Z] [ParacompactSpace Z] :
    Type (u + 1) where
  /-- The ep-groupoid. -/
  X : EP.{u}
  /-- The homeomorphism `β : |X| → Z`. -/
  β : X.X.OrbitSpace ≃ₜ Z

namespace WeakPolyfoldStructure

variable {Z : Type u} [TopologicalSpace Z] [ParacompactSpace Z] (p : WeakPolyfoldStructure Z)

/-- **After Definition 17.1.17**: the paracompactness of `Z` implies that `|X|` is paracompact. -/
theorem hasParacompactOrbitSpace : p.X.X.HasParacompactOrbitSpace :=
  p.β.isClosedEmbedding.paracompactSpace

/-- **After Definition 17.1.17**: `|X|` is metrizable (Theorem 7.3.1). -/
theorem metrizableSpace_orbitSpace : TopologicalSpace.MetrizableSpace p.X.X.OrbitSpace :=
  p.X.X.theorem_7_3_1_metrizable p.hasParacompactOrbitSpace

include p in
/-- **After Definition 17.1.17**: `Z` is metrizable ("only metrizable topological spaces can have
this structure"). -/
theorem metrizableSpace : TopologicalSpace.MetrizableSpace Z := by
  have := p.metrizableSpace_orbitSpace
  exact p.β.symm.isEmbedding.metrizableSpace

/-- The pair `(X, β)` of Remark 10.3.18. -/
def toOrbitChart : OrbitChart Z := ⟨p.X, p.β⟩

end WeakPolyfoldStructure

/-- A polyfold structure in the sense of Definition 16.1.1 is a weak polyfold structure. -/
def PolyfoldStructure.toWeakPolyfoldStructure {Z : Type u} [TopologicalSpace Z]
    [ParacompactSpace Z] (p : PolyfoldStructure Z) : WeakPolyfoldStructure Z :=
  ⟨p.X, p.β⟩

namespace GCT

variable {C : GCT.{u}}

/-- `|C|` is paracompact (it is metrizable, Definition 17.1.1). -/
instance paracompactSpace_orbitSpace : ParacompactSpace C.toGroupoidStr.OrbitSpace :=
  paracompactSpace_of_metrizableSpace _

namespace PolyfoldConstruction

variable (S : C.PolyfoldConstruction) {ι : Type u} (Ψ : ι → S.Unif)

/-! ### The functor `Γ_Ψ` (17.10) -/

/-- **The functor `Γ_Ψ : X_Ψ → C`** (2021 (17.10), p. 754): `q_λ ↦ Ψ_λ(q_λ)`,
`(q_λ, φ, q_λ') ↦ φ`. -/
def modelFunctor : GroupoidFunctor (S.modelEP Ψ).X.toGroupoidStr C.toGroupoidStr where
  obj := S.modelObjMap Ψ
  mor φ := φ.2.mor
  src_mor φ := φ.2.src_mor
  tgt_mor φ := φ.2.tgt_mor
  mor_comp _ _ h := modelGroupoid_comp_mor h
  mor_unit _ := rfl

@[simp] theorem modelFunctor_obj (x : S.ModelObj Ψ) :
    (S.modelFunctor Ψ).obj x = (Ψ x.1).1.obj x.2 := rfl

@[simp] theorem modelFunctor_mor (φ : S.ModelMor Ψ) : (S.modelFunctor Ψ).mor φ = φ.2.mor := rfl

/-- The footprints of the family cover `|C|` (a covering set, p. 752). -/
def IsCoveringFamily : Prop := ⋃ i, (Ψ i).1.footprint = univ

theorem CoveringFamily.isCoveringFamily (c : S.CoveringFamily) : S.IsCoveringFamily c.Ψ :=
  c.cover

/-- **Lemma 17.1.15, fullness**: every `ψ : Ψ_λ(q_λ) → Ψ_λ'(q_λ')` is `Γ_Ψ(q_λ, ψ, q_λ')`. -/
theorem modelFunctor_full : (S.modelFunctor Ψ).toFunctor.Full :=
  (GroupoidFunctor.full_iff _).2 fun x x' ψ hs ht =>
    ⟨⟨(x.1, x'.1), ⟨x.2, ψ, x'.2, hs, ht⟩⟩, rfl, rfl, rfl⟩

/-- **Lemma 17.1.15, faithfulness**: a morphism of `X_Ψ` is determined by its source, target and
the morphism of `C`. -/
theorem modelFunctor_faithful : (S.modelFunctor Ψ).toFunctor.Faithful :=
  (GroupoidFunctor.faithful_iff _).2 fun _ _ hs ht he =>
    (S.modelMorEquiv Ψ).injective (GroupoidStr.TransitionSet.ext hs he ht)

variable {S Ψ} in
/-- **Lemma 17.1.15, essential surjectivity**: since the footprints cover `|C|`, every object of
`C` is isomorphic to some `Ψ_λ(q_λ)`. -/
theorem modelFunctor_essSurj (h : S.IsCoveringFamily Ψ) : (S.modelFunctor Ψ).toFunctor.EssSurj := by
  refine (GroupoidFunctor.essSurj_iff _).2 fun α => ?_
  obtain ⟨i, hi⟩ := mem_iUnion.1 (h.symm ▸ mem_univ (C.toGroupoidStr.π α))
  obtain ⟨q, hq⟩ := (Ψ i).1.mem_footprint_iff.1 hi
  obtain ⟨φ, hs, ht⟩ := (GroupoidStr.π_eq_π_iff _).1 hq
  exact ⟨⟨i, q⟩, φ, hs, ht⟩

/-- `|Γ_Ψ| ∘ π = (q_λ ↦ |Ψ_λ(q_λ)|)`. -/
theorem modelOrbitMap_π (x : S.ModelObj Ψ) :
    (S.modelFunctor Ψ).orbitMap ((S.modelEP Ψ).X.π x) = C.toGroupoidStr.π ((Ψ x.1).1.obj x.2) :=
  rfl

/-- `|Γ_Ψ|` is continuous. -/
theorem continuous_modelOrbitMap : Continuous (S.modelFunctor Ψ).orbitMap :=
  (S.modelEP Ψ).X.proposition_7_1_8_isOpenQuotientMap.isQuotientMap.continuous_iff.2
    (continuous_sigma fun i => (Ψ i).1.continuous_π_obj)

/-- `|Γ_Ψ|` is open: on `|O_λ|` it is `|a| ↦ |Ψ_λ(a)|`, a homeomorphism onto an open subset. -/
theorem isOpenMap_modelOrbitMap : IsOpenMap (S.modelFunctor Ψ).orbitMap := by
  intro W hW
  have he : (S.modelFunctor Ψ).orbitMap '' W = ⋃ i, (fun q : (Ψ i).1.O =>
      C.toGroupoidStr.π ((Ψ i).1.obj q)) '' ((fun q => (S.modelEP Ψ).X.π ⟨i, q⟩) ⁻¹' W) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨⟨i, q⟩, rfl⟩ := (S.modelEP Ψ).X.surjective_π w
      exact mem_iUnion.2 ⟨i, q, hw, rfl⟩
    · intro hz
      obtain ⟨i, q, hq, rfl⟩ := mem_iUnion.1 hz
      exact ⟨_, hq, rfl⟩
  rw [he]
  exact isOpen_iUnion fun i => (Ψ i).1.isOpenMap_π_obj _
    (hW.preimage ((S.modelEP Ψ).X.continuous_π.comp continuous_sigmaMk))

variable {S Ψ} in
/-- `|Γ_Ψ|` is a homeomorphism for a covering family. -/
theorem isHomeomorph_modelOrbitMap (h : S.IsCoveringFamily Ψ) :
    IsHomeomorph (S.modelFunctor Ψ).orbitMap := by
  have : (S.modelFunctor Ψ).toFunctor.IsEquivalence :=
    { faithful := S.modelFunctor_faithful Ψ, full := S.modelFunctor_full Ψ,
      essSurj := modelFunctor_essSurj h }
  exact ⟨S.continuous_modelOrbitMap Ψ, S.isOpenMap_modelOrbitMap Ψ,
    GroupoidFunctor.bijective_orbitMap_of_isEquivalence _ this⟩

variable {S Ψ} in
/-- **Lemma 17.1.15** for a family whose footprints cover `|C|`. -/
theorem lemma_17_1_15_of_isCovering (h : S.IsCoveringFamily Ψ) :
    (S.modelFunctor Ψ).toFunctor.IsEquivalence ∧ IsHomeomorph (S.modelFunctor Ψ).orbitMap :=
  ⟨{ faithful := S.modelFunctor_faithful Ψ, full := S.modelFunctor_full Ψ,
      essSurj := modelFunctor_essSurj h }, isHomeomorph_modelOrbitMap h⟩

/-- **2021 Lemma 17.1.15, p. 754**: for a covering set `Ψ` of uniformizers, the functor
`Γ_Ψ : X_Ψ → C` is an equivalence of categories and `|Γ_Ψ| : |X_Ψ| → |C|` is a homeomorphism. -/
theorem lemma_17_1_15 (c : S.CoveringFamily) :
    (S.modelFunctor c.Ψ).toFunctor.IsEquivalence ∧
      IsHomeomorph (S.modelFunctor c.Ψ).orbitMap :=
  lemma_17_1_15_of_isCovering c.cover

/-- **`|Γ_Ψ| : |X_Ψ| → |C|` as a homeomorphism** (2021 (17.12)). -/
def modelOrbitHomeomorph (c : S.CoveringFamily) :
    (S.modelEP c.Ψ).X.OrbitSpace ≃ₜ C.toGroupoidStr.OrbitSpace :=
  (S.lemma_17_1_15 c).2.homeomorph

@[simp] theorem modelOrbitHomeomorph_apply (c : S.CoveringFamily)
    (z : (S.modelEP c.Ψ).X.OrbitSpace) :
    S.modelOrbitHomeomorph c z = (S.modelFunctor c.Ψ).orbitMap z := rfl

/-! ### Remark 17.1.16 -/

/-- **Remark 17.1.16**: since `|C|` is metrizable, so is `|X_Ψ|`. -/
theorem metrizableSpace_modelOrbitSpace (c : S.CoveringFamily) :
    TopologicalSpace.MetrizableSpace (S.modelEP c.Ψ).X.OrbitSpace :=
  (S.modelOrbitHomeomorph c).isEmbedding.metrizableSpace

/-- **Remark 17.1.16**: `X_Ψ` is an ep-groupoid with paracompact orbit space. -/
theorem hasParacompactOrbitSpace_model (c : S.CoveringFamily) :
    (S.modelEP c.Ψ).X.HasParacompactOrbitSpace := by
  have := S.metrizableSpace_modelOrbitSpace c
  exact paracompactSpace_of_metrizableSpace _

/-- **Remark 17.1.16**: if `X_Ψ` satisfies (ZHOU), `(X_Ψ, |Γ_Ψ|)` is a polyfold structure on `|C|`
in the sense of Definition 16.1.1. -/
def modelPolyfoldStructure (c : S.CoveringFamily) (hZ : (S.modelEP c.Ψ).X.IsZhou) :
    PolyfoldStructure C.toGroupoidStr.OrbitSpace :=
  ⟨S.modelEP c.Ψ, S.hasParacompactOrbitSpace_model c, hZ, S.modelOrbitHomeomorph c⟩

/-- **2021 Remark 17.1.16, p. 755**: `|X_Ψ|` is metrizable and paracompact, and if `X_Ψ` satisfies
(ZHOU), `(X_Ψ, |Γ_Ψ|)` is a polyfold structure on `|C|` (Definition 16.1.1). -/
theorem remark_17_1_16 (c : S.CoveringFamily) :
    TopologicalSpace.MetrizableSpace (S.modelEP c.Ψ).X.OrbitSpace ∧
      (S.modelEP c.Ψ).X.HasParacompactOrbitSpace ∧
      ∀ hZ : (S.modelEP c.Ψ).X.IsZhou, (S.modelPolyfoldStructure c hZ).X = S.modelEP c.Ψ ∧
        ⇑(S.modelPolyfoldStructure c hZ).β = (S.modelFunctor c.Ψ).orbitMap :=
  ⟨S.metrizableSpace_modelOrbitSpace c, S.hasParacompactOrbitSpace_model c,
    fun _ => ⟨rfl, rfl⟩⟩

/-! ### (17.13) -/

/-- **(17.13), p. 755**: `(X_Ψ, |Γ_Ψ|)` is a weak polyfold structure on `|C|`
(Definition 17.1.17). -/
def weakStructure (c : S.CoveringFamily) : WeakPolyfoldStructure C.toGroupoidStr.OrbitSpace :=
  ⟨S.modelEP c.Ψ, S.modelOrbitHomeomorph c⟩

@[simp] theorem weakStructure_X (c : S.CoveringFamily) :
    (S.weakStructure c).X = S.modelEP c.Ψ := rfl

@[simp] theorem weakStructure_β (c : S.CoveringFamily) :
    ⇑(S.weakStructure c).β = (S.modelFunctor c.Ψ).orbitMap := rfl

end PolyfoldConstruction

end GCT

end Polyfold
