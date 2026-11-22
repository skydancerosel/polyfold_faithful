import Polyfold.Chapter17.LocalUniformizer

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.1 (pp. 746–752): **Definition 17.1.6** (uniformizer construction), **Definition 17.1.8**
(polyfold structure `(F, M)`, tame, polyfold), **Lemma 17.1.9**, the admissible triples and
natural charts (17.6), **Lemma 17.1.13**, and the covering families of p. 752.  Numbers and pages
are the 2021 text's.

# Polyfold structures on a GCT

## The text, paraphrased

(Definition 17.1.6, p. 746) `C⁻` keeps the objects of `C` and only the identities; a uniformizer
construction is a functor `F : C⁻ → SET` associating to `α` a set `F(α)` of local uniformizers at
`α`.  (Definition 17.1.8, p. 747) A polyfold structure for the GCT `C` consists of (1) a uniformizer
construction `F`, and (2) an M-polyfold structure on every transition set `M(Ψ, Ψ')`, `Ψ ∈ F(α)`,
`Ψ' ∈ F(α')`, such that (a) `s : M(Ψ, Ψ') → O` and `t : M(Ψ, Ψ') → O'` are local
sc-diffeomorphisms, (b) `u : O → M(Ψ, Ψ)` and `ι : M(Ψ, Ψ') → M(Ψ', Ψ)` are sc-smooth, (c) the
multiplication `M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ') → M(Ψ, Ψ'')` is sc-smooth.  If all its local uniformizers
are tame, `(F, M)` is a tame polyfold construction; a polyfold is a GCT with a polyfold structure.
(Lemma 17.1.9, p. 748) For `Ψ ∈ F(α)`, `Ψ(q) = α`, the map `Ψ̂ : G ⋉ O → M(Ψ, Ψ)`,
`(g, p) ↦ (p, Ψ(g, p), g ∗ p)` is an sc-diffeomorphism; `U(q, g, q)` (on which
`s : U(q, g, q) → O` is an sc-diffeomorphism) are pairwise disjoint open sets, `M(Ψ, Ψ)` is their
union, and `t(p, φ, p') = g ∗ p` on `U(q, g, q)`.  The proof: `Ψ̂` is a bijection; "from
`s ∘ Ψ̂(g, p) = p` we conclude that `Ψ̂` is a local sc-diffeomorphism, since `s` has this property".
(p. 752) Every `(o, φ, o') ∈ M(Ψ, Ψ')` has open `U(o)`, `U(o, φ, o')`, `U(o')` with `s` and `t`
sc-diffeomorphisms (17.6), an admissible triple; `s|U(o, φ, o')` is a natural source-type chart,
`t|U(o, φ, o')` a natural target-type chart.  (Lemma 17.1.13) The transition maps between natural
source-type (target-type) charts are the identity.  (p. 752) A covering set of uniformizers is a
family `(Ψ_λ)` in the `F(α)` whose footprints cover `|C|`.

## What is formalized (namespace `Polyfold.GCT`)

* `MPolyfold.IsScSmoothOnFibredProduct`: sc-smoothness of a map on the sub-M-polyfold
  `A ₓ×_g B` (Definition 17.1.8 (c), the three-space form of `EpGroupoid.IsScSmoothComp`).
* `UniformizerConstruction C` (**Definition 17.1.6**): `F : C.Obj → Set C.LocalUniformizer` with
  `isAt`; `Unif F` (the uniformizers associated to `F`); `HasUniformizers` (`F(α) ≠ ∅` for every
  `α`), `HasCoveringUniformizers` (the footprints cover `|C|`), `CoveringFamily` (p. 752),
  `exists_coveringFamily_iff`, `hasCoveringUniformizers_of_hasUniformizers`.
* `PolyfoldConstruction C` (**Definition 17.1.8**): the uniformizer construction, the topologies
  `topM` and M-polyfold structures `M Ψ Ψ'` on the transition sets, and (a) `isLocalScDiffeo_src`,
  `isLocalScDiffeo_tgt`, (b) `isScSmoothMap_unit`, `isScSmoothMap_inv`, (c) `isScSmoothMap_mul`.
  The type synonym `Tr Ψ Ψ'` carries the instances, with `transPolyfold`; the conditions restated on
  it (`isLocalScDiffeo_trSrc`, …); `IsTame` (tame polyfold construction); `CategoryPolyfold`
  (a polyfold: a GCT with a polyfold structure).
* `AdmissibleTriple` (17.6), `exists_admissibleTriple`; **Lemma 17.1.13** (`lemma_17_1_13`).
* **Lemma 17.1.9**: `hat` (`Ψ̂` into `Tr Ψ Ψ`), `lemma_17_1_9_bijective`, the sheets `hatSheet Ψ g`
  (`U(q, g, q) = Ψ̂({g} × O)`), `lemma_17_1_9_decomposition` (pairwise disjoint, covering, `t = g ∗`
  on them; no topology needed), and `lemma_17_1_9_of_continuous`: if `Ψ̂` is continuous, it is an
  sc-diffeomorphism, the sheets are open and `s` maps each sc-diffeomorphically onto `O`.  Without
  continuity the lemma does not hold as we read it: `not_lemma_17_1_9`
  (`PolyfoldConstructionExamples.lean`).

## Readings

* `C⁻` has only identities, so a functor `C⁻ → SET` is a family of sets `F(α)`; `F(α)` is a set
  of local uniformizers, each at `α` (`isAt`).
* The M-polyfold structure on `M(Ψ, Ψ')` depends on the uniformizers `Ψ, Ψ'` (the text's notation
  `M(Ψ, Ψ')`), not on the objects `α, α'`; it is given for the uniformizers `Unif F` of `F`.
* (c) is asked literally on the sub-M-polyfold `M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ')` of the product (a
  sub-M-polyfold since `s` is a local sc-diffeomorphism, Proposition 2.5.20).
* The text picks covering sets without comment (p. 752).  This needs every isomorphism class to
  meet a footprint, which nothing in Definitions 17.1.6, 17.1.8 asks; we record it as the named
  hypotheses `HasCoveringUniformizers` (equivalent to the existence of a covering family) and the
  stronger `HasUniformizers` (`F(α) ≠ ∅` for all `α`).  With `F ≡ ∅` on a non-empty `C` there is no
  covering family (`not_hasCoveringUniformizers_empty`, `PolyfoldConstructionExamples.lean`).
* Lemma 17.1.9: "`U(q, g, q)` characterized by the property that `s` is an sc-diffeomorphism" does
  not single out a set; we read `U(q, g, q)` as `Ψ̂({g} × O)`, as the proof does.  The step "`Ψ̂` is
  a local sc-diffeomorphism since `s` is one" needs `Ψ̂` to be continuous; we prove the lemma under
  that hypothesis (`_of_continuous`) and show that Definition 17.1.8 does not imply it.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology CategoryTheory

noncomputable section

namespace Polyfold

universe u

/-! ### Sc-smoothness on a fibred product of three M-polyfolds -/

namespace MPolyfold

variable {A B Z D : Type u} [TopologicalSpace A] [T2Space A] [ParacompactSpace A]
  [TopologicalSpace B] [T2Space B] [ParacompactSpace B] [TopologicalSpace Z] [T2Space Z]
  [ParacompactSpace Z] [TopologicalSpace D] [T2Space D] [ParacompactSpace D]

/-- A map `h : A ₓ×_g B → D` on the fibred product of a local sc-diffeomorphism `f : A → Z` and an
sc-smooth `g : B → Z` is **sc-smooth**: sc-smooth on the sub-M-polyfold `A ₓ×_g B` of `A × B`
(Proposition 2.5.20; Definition 17.1.8 (c)). -/
def IsScSmoothOnFibredProduct (PA : MPolyfold A) (PB : MPolyfold B) (PD : MPolyfold D)
    {PZ : MPolyfold Z} {f : A → Z} {g : B → Z} (hf : PA.IsLocalScDiffeo PZ f)
    (hg : PB.IsScSmoothMap PZ g) (h : fibredProduct f g → D) : Prop :=
  letI := MPolyfold.paracompactSpace_prod PA PB
  letI := (PA.prod PB).paracompactSpace_subtype (fibredProduct f g)
  (subPolyfold (isSubMPolyfold_fibredProduct hf hg)).IsScSmoothMap PD h

end MPolyfold

namespace GCT

variable {C : GCT.{u}}

/-- The uniformizers associated to `F`: those lying in some `F(α)`. -/
def Unif (F : C.Obj → Set C.LocalUniformizer) : Type (u + 1) := {Ψ // ∃ α, Ψ ∈ F α}

variable (C) in
/-- **2021 Definition 17.1.6, p. 746**: a **uniformizer construction** `F : C⁻ → SET`, a set
`F(α)` of local uniformizers at `α` for every object `α`. -/
structure UniformizerConstruction : Type (u + 1) where
  /-- The sets `F(α)`. -/
  F : C.Obj → Set C.LocalUniformizer
  /-- Every `Ψ ∈ F(α)` is a local uniformizer at `α`. -/
  isAt : ∀ α, ∀ Ψ ∈ F α, Ψ.IsAt α

namespace UniformizerConstruction

variable (U : C.UniformizerConstruction)

/-- The uniformizers of `U`. -/
abbrev Unif : Type (u + 1) := GCT.Unif U.F

/-- **Every object has a uniformizer**: `F(α) ≠ ∅` for every `α` (implicit in the text). -/
def HasUniformizers : Prop := ∀ α, (U.F α).Nonempty

/-- **The footprints of `F` cover `|C|`**: every isomorphism class meets the footprint of a
uniformizer of `F` (implicit in the choice of a covering set, p. 752). -/
def HasCoveringUniformizers : Prop := ⋃ Ψ : U.Unif, Ψ.1.footprint = univ

/-- **A covering set of uniformizers** (2021 p. 752): a family `(Ψ_λ)_{λ ∈ Λ}` of uniformizers of
`F` whose footprints cover `|C|`. -/
structure CoveringFamily : Type (u + 1) where
  /-- The index set `Λ`. -/
  ι : Type u
  /-- The uniformizers `Ψ_λ`. -/
  Ψ : ι → U.Unif
  /-- `|C| = ⋃ footprint(Ψ_λ)`. -/
  cover : ⋃ i, (Ψ i).1.footprint = univ

theorem hasCoveringUniformizers_of_hasUniformizers (h : U.HasUniformizers) :
    U.HasCoveringUniformizers := by
  refine eq_univ_of_forall fun z => ?_
  induction z using Quotient.inductionOn with
  | h α =>
    obtain ⟨Ψ, hΨ⟩ := h α
    exact mem_iUnion.2 ⟨⟨Ψ, α, hΨ⟩, Ψ.mem_footprint_of_isAt (U.isAt α Ψ hΨ)⟩

/-- **A covering family exists iff the footprints of `F` cover `|C|`** (index set `|C|`). -/
theorem exists_coveringFamily_iff : Nonempty U.CoveringFamily ↔ U.HasCoveringUniformizers := by
  constructor
  · rintro ⟨c⟩
    refine eq_univ_of_forall fun z => ?_
    obtain ⟨i, hi⟩ := mem_iUnion.1 (c.cover.symm ▸ mem_univ z)
    exact mem_iUnion.2 ⟨c.Ψ i, hi⟩
  · intro h
    have hz : ∀ z, ∃ Ψ : U.Unif, z ∈ Ψ.1.footprint := fun z =>
      mem_iUnion.1 (h.symm ▸ mem_univ z)
    exact ⟨⟨C.toGroupoidStr.OrbitSpace, fun z => (hz z).choose,
      eq_univ_of_forall fun z => mem_iUnion.2 ⟨z, (hz z).choose_spec⟩⟩⟩

end UniformizerConstruction

variable (C) in
/-- **2021 Definition 17.1.8, p. 747**: a **polyfold structure** `(F, M)` for the GCT `C`:
(1) a uniformizer construction `F`, (2) an M-polyfold structure `M Ψ Ψ'` on every transition set
`M(Ψ, Ψ')` of uniformizers of `F`, such that (a) `s` and `t` are local sc-diffeomorphisms, (b) the
unit map `u : O → M(Ψ, Ψ)` and the inversion `ι : M(Ψ, Ψ') → M(Ψ', Ψ)` are sc-smooth, and (c) the
multiplication `M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ') → M(Ψ, Ψ'')` is sc-smooth. -/
structure PolyfoldConstruction : Type (u + 1) extends C.UniformizerConstruction where
  /-- The topology of `M(Ψ, Ψ')`. -/
  [topM : ∀ Ψ Ψ' : GCT.Unif F, TopologicalSpace (Ψ.1.Trans Ψ'.1)]
  [t2M : ∀ Ψ Ψ' : GCT.Unif F, T2Space (Ψ.1.Trans Ψ'.1)]
  [paraM : ∀ Ψ Ψ' : GCT.Unif F, ParacompactSpace (Ψ.1.Trans Ψ'.1)]
  /-- (2) The M-polyfold structure of `M(Ψ, Ψ')`. -/
  M : ∀ Ψ Ψ' : GCT.Unif F, MPolyfold (Ψ.1.Trans Ψ'.1)
  /-- (a) `s : M(Ψ, Ψ') → O` is a local sc-diffeomorphism. -/
  isLocalScDiffeo_src : ∀ Ψ Ψ' : GCT.Unif F,
    (M Ψ Ψ').IsLocalScDiffeo Ψ.1.P GroupoidStr.TransitionSet.src
  /-- (a) `t : M(Ψ, Ψ') → O'` is a local sc-diffeomorphism. -/
  isLocalScDiffeo_tgt : ∀ Ψ Ψ' : GCT.Unif F,
    (M Ψ Ψ').IsLocalScDiffeo Ψ'.1.P GroupoidStr.TransitionSet.tgt
  /-- (b) The unit map `u : O → M(Ψ, Ψ)` is sc-smooth. -/
  isScSmoothMap_unit : ∀ Ψ : GCT.Unif F,
    Ψ.1.P.IsScSmoothMap (M Ψ Ψ) GroupoidStr.TransitionSet.unit
  /-- (b) The inversion `ι : M(Ψ, Ψ') → M(Ψ', Ψ)` is sc-smooth. -/
  isScSmoothMap_inv : ∀ Ψ Ψ' : GCT.Unif F,
    (M Ψ Ψ').IsScSmoothMap (M Ψ' Ψ) GroupoidStr.TransitionSet.inv
  /-- (c) The multiplication `m : M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ') → M(Ψ, Ψ'')` is sc-smooth. -/
  isScSmoothMap_mul : ∀ Ψ Ψ' Ψ'' : GCT.Unif F,
    MPolyfold.IsScSmoothOnFibredProduct (M Ψ' Ψ'') (M Ψ Ψ') (M Ψ Ψ'')
      (isLocalScDiffeo_src Ψ' Ψ'') (isLocalScDiffeo_tgt Ψ Ψ').isScSmoothMap
      GroupoidStr.TransitionSet.mul

namespace PolyfoldConstruction

variable (S : C.PolyfoldConstruction)

/-- The uniformizers of `S`. -/
abbrev Unif : Type (u + 1) := GCT.Unif S.F

/-- **The transition M-polyfold `M(Ψ, Ψ')`** of `S` (a type synonym of the transition set that
carries the topology and the M-polyfold structure of Definition 17.1.8 (2)). -/
def Tr (Ψ Ψ' : S.Unif) : Type u := Ψ.1.Trans Ψ'.1

instance (Ψ Ψ' : S.Unif) : TopologicalSpace (S.Tr Ψ Ψ') := S.topM Ψ Ψ'
instance (Ψ Ψ' : S.Unif) : T2Space (S.Tr Ψ Ψ') := S.t2M Ψ Ψ'
instance (Ψ Ψ' : S.Unif) : ParacompactSpace (S.Tr Ψ Ψ') := S.paraM Ψ Ψ'

/-- The M-polyfold structure of `M(Ψ, Ψ')`. -/
def transPolyfold (Ψ Ψ' : S.Unif) : MPolyfold (S.Tr Ψ Ψ') := S.M Ψ Ψ'

/-- An element of `M(Ψ, Ψ')` as an element of the transition M-polyfold. -/
abbrev toTr {Ψ Ψ' : S.Unif} (a : Ψ.1.Trans Ψ'.1) : S.Tr Ψ Ψ' := a

instance (Ψ Ψ' : S.Unif) : TopologicalSpace.MetrizableSpace (S.Tr Ψ Ψ') :=
  (S.transPolyfold Ψ Ψ').metrizableSpace

/-- **Definition 17.1.8 (a)** on `Tr`: `s` is a local sc-diffeomorphism. -/
theorem isLocalScDiffeo_trSrc (Ψ Ψ' : S.Unif) :
    (S.transPolyfold Ψ Ψ').IsLocalScDiffeo Ψ.1.P fun a : S.Tr Ψ Ψ' => a.src :=
  S.isLocalScDiffeo_src Ψ Ψ'

/-- **Definition 17.1.8 (a)** on `Tr`: `t` is a local sc-diffeomorphism. -/
theorem isLocalScDiffeo_trTgt (Ψ Ψ' : S.Unif) :
    (S.transPolyfold Ψ Ψ').IsLocalScDiffeo Ψ'.1.P fun a : S.Tr Ψ Ψ' => a.tgt :=
  S.isLocalScDiffeo_tgt Ψ Ψ'

theorem continuous_trSrc (Ψ Ψ' : S.Unif) : Continuous fun a : S.Tr Ψ Ψ' => a.src :=
  (S.isLocalScDiffeo_trSrc Ψ Ψ').continuous

theorem continuous_trTgt (Ψ Ψ' : S.Unif) : Continuous fun a : S.Tr Ψ Ψ' => a.tgt :=
  (S.isLocalScDiffeo_trTgt Ψ Ψ').continuous

/-- **Definition 17.1.8 (b)** on `Tr`: the unit map is sc-smooth. -/
theorem isScSmoothMap_trUnit (Ψ : S.Unif) :
    Ψ.1.P.IsScSmoothMap (S.transPolyfold Ψ Ψ) fun q => S.toTr (GroupoidStr.TransitionSet.unit q) :=
  S.isScSmoothMap_unit Ψ

/-- **Definition 17.1.8 (b)** on `Tr`: the inversion is sc-smooth. -/
theorem isScSmoothMap_trInv (Ψ Ψ' : S.Unif) :
    (S.transPolyfold Ψ Ψ').IsScSmoothMap (S.transPolyfold Ψ' Ψ)
      fun a : S.Tr Ψ Ψ' => S.toTr (GroupoidStr.TransitionSet.inv a) :=
  S.isScSmoothMap_inv Ψ Ψ'

/-- **Definition 17.1.8 (c)** on `Tr`: the multiplication is sc-smooth. -/
theorem isScSmoothMap_trMul (Ψ Ψ' Ψ'' : S.Unif) :
    MPolyfold.IsScSmoothOnFibredProduct (S.transPolyfold Ψ' Ψ'') (S.transPolyfold Ψ Ψ')
      (S.transPolyfold Ψ Ψ'') (S.isLocalScDiffeo_trSrc Ψ' Ψ'')
      (S.isLocalScDiffeo_trTgt Ψ Ψ').isScSmoothMap
      fun p => S.toTr (GroupoidStr.TransitionSet.mul p) :=
  S.isScSmoothMap_mul Ψ Ψ' Ψ''

/-- **Definition 17.1.8**: a **tame polyfold construction**: all local uniformizers associated to
`F` are tame. -/
def IsTame : Prop := ∀ α, ∀ Ψ ∈ S.F α, Ψ.IsTame

/-- The covering families of `S` (p. 752). -/
abbrev CoveringFamily : Type (u + 1) := S.toUniformizerConstruction.CoveringFamily

/-- `F(α) ≠ ∅` for every `α`. -/
abbrev HasUniformizers : Prop := S.toUniformizerConstruction.HasUniformizers

/-- The footprints of `F` cover `|C|`. -/
abbrev HasCoveringUniformizers : Prop := S.toUniformizerConstruction.HasCoveringUniformizers

/-! ### Admissible triples and natural charts (17.6), Lemma 17.1.13 -/

/-- **An admissible triple** `(U(o), U(o, φ, o'), U(o'))` at `a = (o, φ, o') ∈ M(Ψ, Ψ')`
(2021 (17.6), p. 752): open sets with `s : U(o, φ, o') → U(o)` and `t : U(o, φ, o') → U(o')`
sc-diffeomorphisms.  `s|U(o, φ, o')` is a natural source-type chart, `t|U(o, φ, o')` a natural
target-type chart. -/
structure AdmissibleTriple {Ψ Ψ' : S.Unif} (a : S.Tr Ψ Ψ') where
  /-- `U(o)`. -/
  srcSet : Set Ψ.1.O
  /-- `U(o, φ, o')`. -/
  carrier : Set (S.Tr Ψ Ψ')
  /-- `U(o')`. -/
  tgtSet : Set Ψ'.1.O
  /-- `(s|U(o, φ, o'))⁻¹`. -/
  srcInv : Ψ.1.O → S.Tr Ψ Ψ'
  /-- `(t|U(o, φ, o'))⁻¹`. -/
  tgtInv : Ψ'.1.O → S.Tr Ψ Ψ'
  mem_carrier : a ∈ carrier
  isScDiffeoOn_src : (S.transPolyfold Ψ Ψ').IsScDiffeoOn Ψ.1.P (fun b : S.Tr Ψ Ψ' => b.src)
    srcInv carrier srcSet
  isScDiffeoOn_tgt : (S.transPolyfold Ψ Ψ').IsScDiffeoOn Ψ'.1.P (fun b : S.Tr Ψ Ψ' => b.tgt)
    tgtInv carrier tgtSet

/-- **Every element of `M(Ψ, Ψ')` has an admissible triple** (2021 p. 752; from (a)). -/
theorem exists_admissibleTriple {Ψ Ψ' : S.Unif} (a : S.Tr Ψ Ψ') :
    Nonempty (S.AdmissibleTriple a) := by
  obtain ⟨W₁, V₁, σ₁, ha₁, h₁⟩ := S.isLocalScDiffeo_trSrc Ψ Ψ' a
  obtain ⟨W₂, V₂, σ₂, ha₂, h₂⟩ := S.isLocalScDiffeo_trTgt Ψ Ψ' a
  have hW : IsOpen (W₁ ∩ W₂) := h₁.isOpen_source.inter h₂.isOpen_source
  exact ⟨⟨_, W₁ ∩ W₂, _, σ₁, σ₂, ⟨ha₁, ha₂⟩, h₁.restrict hW inter_subset_left,
    h₂.restrict hW inter_subset_right⟩⟩

/-- **2021 Lemma 17.1.13, p. 752**: for two natural source-type charts `s₁, s₂` of `M(Ψ, Ψ')` the
transition map `s₂ ∘ s₁⁻¹` is the identity on `s₁(U₁ ∩ U₂)`; the same holds for natural
target-type charts. -/
theorem lemma_17_1_13 {Ψ Ψ' : S.Unif} {a₁ a₂ : S.Tr Ψ Ψ'} (T₁ : S.AdmissibleTriple a₁)
    (T₂ : S.AdmissibleTriple a₂) :
    EqOn ((fun b : S.Tr Ψ Ψ' => b.src) ∘ T₁.srcInv) id
        ((fun b : S.Tr Ψ Ψ' => b.src) '' (T₁.carrier ∩ T₂.carrier)) ∧
      EqOn ((fun b : S.Tr Ψ Ψ' => b.tgt) ∘ T₁.tgtInv) id
        ((fun b : S.Tr Ψ Ψ' => b.tgt) '' (T₁.carrier ∩ T₂.carrier)) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    exact congrArg (fun b : S.Tr Ψ Ψ' => b.src) (T₁.isScDiffeoOn_src.left_inv b hb.1)
  · rintro _ ⟨b, hb, rfl⟩
    exact congrArg (fun b : S.Tr Ψ Ψ' => b.tgt) (T₁.isScDiffeoOn_tgt.left_inv b hb.1)

/-! ### Lemma 17.1.9 -/

/-- **The map `Ψ̂ : G ⋉ O → M(Ψ, Ψ)` of 2021 Lemma 17.1.9, (17.1)**, into the transition
M-polyfold: `(g, p) ↦ (p, Ψ(g, p), g ∗ p)`. -/
def hat (Ψ : S.Unif) : Ψ.1.G × Ψ.1.O → S.Tr Ψ Ψ := Ψ.1.toUniformizer.hat

/-- The inverse of `Ψ̂`. -/
def hatInv (Ψ : S.Unif) : S.Tr Ψ Ψ → Ψ.1.G × Ψ.1.O := Ψ.1.toUniformizer.hatEquiv.symm

theorem hat_hatInv (Ψ : S.Unif) (a : S.Tr Ψ Ψ) : S.hat Ψ (S.hatInv Ψ a) = a :=
  Ψ.1.toUniformizer.hatEquiv.apply_symm_apply a

theorem hatInv_hat (Ψ : S.Unif) (p : Ψ.1.G × Ψ.1.O) : S.hatInv Ψ (S.hat Ψ p) = p :=
  Ψ.1.toUniformizer.hatEquiv.symm_apply_apply p

/-- **2021 Lemma 17.1.9, p. 748, the first step of the proof**: `Ψ̂` is a bijection. -/
theorem lemma_17_1_9_bijective (Ψ : S.Unif) : Bijective (S.hat Ψ) :=
  Ψ.1.toUniformizer.hat_bijective

/-- **The sheet `U(q, g, q)` of 2021 Lemma 17.1.9**: `Ψ̂({g} × O)`. -/
def hatSheet (Ψ : S.Unif) (g : Ψ.1.G) : Set (S.Tr Ψ Ψ) := S.hat Ψ '' ({g} ×ˢ univ)

/-- **2021 Lemma 17.1.9, p. 748, the decomposition** (no topology needed): the sheets
`U(q, g, q) = Ψ̂({g} × O)` are pairwise disjoint, `M(Ψ, Ψ)` is their union, and
`t(p, φ, p') = g ∗ p` on `U(q, g, q)`; `Ψ̂(g, q) ∈ U(q, g, q)`. -/
theorem lemma_17_1_9_decomposition (Ψ : S.Unif) :
    Pairwise (Disjoint on S.hatSheet Ψ) ∧ (⋃ g, S.hatSheet Ψ g) = univ ∧
      (∀ g, ∀ a ∈ S.hatSheet Ψ g, a.tgt = g • a.src) ∧ ∀ g q, S.hat Ψ (g, q) ∈ S.hatSheet Ψ g := by
  refine ⟨fun g g' hgg' => ?_, ?_, ?_, fun g q => ⟨(g, q), ⟨rfl, mem_univ _⟩, rfl⟩⟩
  · refine Set.disjoint_left.2 ?_
    rintro _ ⟨p, hp, rfl⟩ ⟨p', hp', he⟩
    have he' : p' = p := (S.lemma_17_1_9_bijective Ψ).1 he
    have h1 : p.1 = g := hp.1
    have h2 : p'.1 = g' := hp'.1
    exact hgg' (h1.symm.trans ((congrArg Prod.fst he').symm.trans h2))
  · refine eq_univ_of_forall fun a => mem_iUnion.2 ⟨(S.hatInv Ψ a).1,
      ⟨S.hatInv Ψ a, ⟨rfl, mem_univ _⟩, S.hat_hatInv Ψ a⟩⟩
  · rintro g _ ⟨p, hp, rfl⟩
    change p.1 • p.2 = g • p.2
    rw [show p.1 = g from hp.1]

/-- The M-polyfold `G × O` of the morphisms of `G ⋉ O`. -/
abbrev morPolyfold (Ψ : S.Unif) : MPolyfold (Ψ.1.G × Ψ.1.O) := Ψ.1.toUniformizer.ep.PMor

theorem src_hat (Ψ : S.Unif) (p : Ψ.1.G × Ψ.1.O) : (S.hat Ψ p).src = p.2 := rfl

theorem tgt_hat (Ψ : S.Unif) (p : Ψ.1.G × Ψ.1.O) : (S.hat Ψ p).tgt = p.1 • p.2 := rfl

/-- If `Ψ̂` is continuous, it is sc-smooth: near `(g, p)` it is `(s|W)⁻¹ ∘ pr₂` for a sheet `W` of
`s` (the step of the proof of Lemma 17.1.9). -/
theorem isScSmoothMap_hat_of_continuous (Ψ : S.Unif) (hc : Continuous (S.hat Ψ)) :
    (S.morPolyfold Ψ).IsScSmoothMap (S.transPolyfold Ψ Ψ) (S.hat Ψ) := by
  refine MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun x _ => ?_
  obtain ⟨W, V, σ, hxW, hd⟩ := S.isLocalScDiffeo_trSrc Ψ Ψ (S.hat Ψ x)
  have hN : IsOpen (({x.1} ×ˢ univ) ∩ S.hat Ψ ⁻¹' W) :=
    (isOpen_sheet x.1).inter (hd.isOpen_source.preimage hc)
  refine ⟨_, hN, ⟨⟨rfl, mem_univ _⟩, hxW⟩, subset_univ _, ?_⟩
  refine (MPolyfold.IsScSmoothOn.comp hd.isScSmoothOn_inv
    ((MPolyfold.isScSmoothMap_snd _ _).mono hN (subset_univ _))
    fun y hy => hd.mapsTo hy.2).congr fun y hy => ?_
  exact hd.left_inv _ hy.2

/-- If `Ψ̂` is continuous, its inverse is sc-smooth: near `a ∈ W` (a sheet of `s` through
`a = Ψ̂(g, p)`), `Ψ̂⁻¹(b) = (g, s(b))`. -/
theorem isScSmoothMap_hatInv_of_continuous (Ψ : S.Unif) (hc : Continuous (S.hat Ψ)) :
    (S.transPolyfold Ψ Ψ).IsScSmoothMap (S.morPolyfold Ψ) (S.hatInv Ψ) := by
  refine MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun a _ => ?_
  obtain ⟨W, V, σ, haW, hd⟩ := S.isLocalScDiffeo_trSrc Ψ Ψ a
  set g := (S.hatInv Ψ a).1
  have hcg : Continuous fun p : Ψ.1.O => S.hat Ψ (g, p) := hc.comp (Continuous.prodMk_right g)
  set V'' := V ∩ (fun p : Ψ.1.O => S.hat Ψ (g, p)) ⁻¹' W
  have hV'' : IsOpen V'' := hd.isOpen_target.inter (hd.isOpen_source.preimage hcg)
  set Oa := W ∩ (fun b : S.Tr Ψ Ψ => b.src) ⁻¹' V''
  have hOa : IsOpen Oa := hd.isOpen_source.inter (hV''.preimage (S.continuous_trSrc Ψ Ψ))
  have haOa : a ∈ Oa := by
    refine ⟨haW, hd.mapsTo haW, ?_⟩
    change S.hat Ψ (g, a.src) ∈ W
    have : (g, a.src) = S.hatInv Ψ a := Prod.ext rfl (by
      conv_lhs => rw [← S.hat_hatInv Ψ a]
      rfl)
    rw [this, S.hat_hatInv]
    exact haW
  have heq : ∀ b ∈ Oa, S.hatInv Ψ b = (g, b.src) := by
    intro b hb
    have h1 : S.hat Ψ (g, b.src) = b := hd.injOn hb.2.2 hb.1 rfl
    exact (congrArg (S.hatInv Ψ) h1).symm.trans (S.hatInv_hat Ψ _)
  refine ⟨Oa, hOa, haOa, subset_univ _, ?_⟩
  refine (MPolyfold.IsScSmoothOn.comp (isScSmoothMap_sheet g)
    ((S.isLocalScDiffeo_trSrc Ψ Ψ).isScSmoothMap.mono hOa (subset_univ _))
    (mapsTo_univ _ _)).congr fun b hb => (heq b hb).symm

/-- **2021 Lemma 17.1.9, p. 748, for continuous `Ψ̂`**: if `Ψ̂ : G ⋉ O → M(Ψ, Ψ)` is continuous,
then it is an sc-diffeomorphism, every sheet `U(q, g, q) = Ψ̂({g} × O)` is open, and
`s : U(q, g, q) → O` is an sc-diffeomorphism (with inverse `p ↦ Ψ̂(g, p)`).  (The decomposition is
`lemma_17_1_9_decomposition`.) -/
theorem lemma_17_1_9_of_continuous (Ψ : S.Unif) (hc : Continuous (S.hat Ψ)) :
    (S.morPolyfold Ψ).IsScDiffeoOn (S.transPolyfold Ψ Ψ) (S.hat Ψ) (S.hatInv Ψ) univ univ ∧
      (∀ g, IsOpen (S.hatSheet Ψ g)) ∧
      ∀ g, (S.transPolyfold Ψ Ψ).IsScDiffeoOn Ψ.1.P (fun a : S.Tr Ψ Ψ => a.src)
        (fun p => S.hat Ψ (g, p)) (S.hatSheet Ψ g) univ := by
  have hs := S.isScSmoothMap_hat_of_continuous Ψ hc
  have hi := S.isScSmoothMap_hatInv_of_continuous Ψ hc
  have hopen : ∀ g, IsOpen (S.hatSheet Ψ g) := fun g => by
    have : S.hatSheet Ψ g = S.hatInv Ψ ⁻¹' ({g} ×ˢ univ) := by
      ext a
      constructor
      · rintro ⟨p, hp, rfl⟩
        rw [mem_preimage, S.hatInv_hat]
        exact hp
      · intro ha
        exact ⟨S.hatInv Ψ a, ha, S.hat_hatInv Ψ a⟩
    rw [this]
    exact (isOpen_sheet g).preimage (continuousOn_univ.1 hi.continuousOn)
  refine ⟨⟨hs, hi, mapsTo_univ _ _, mapsTo_univ _ _, fun p _ => S.hatInv_hat Ψ p,
    fun a _ => S.hat_hatInv Ψ a⟩, hopen, fun g => ⟨?_, ?_, mapsTo_univ _ _, ?_, ?_, ?_⟩⟩
  · exact (S.isLocalScDiffeo_trSrc Ψ Ψ).isScSmoothMap.mono (hopen g) (subset_univ _)
  · exact MPolyfold.IsScSmoothOn.comp hs (isScSmoothMap_sheet g) (mapsTo_univ _ _)
  · intro p _
    exact ⟨(g, p), ⟨rfl, mem_univ _⟩, rfl⟩
  · rintro _ ⟨p, hp, rfl⟩
    change S.hat Ψ (g, p.2) = S.hat Ψ p
    rw [show g = p.1 from hp.1.symm]
  · intro p _
    rfl

end PolyfoldConstruction

end GCT

/-- **2021 Definition 17.1.8, p. 747**: a **polyfold** (in the categorical sense): a GCT `C`
together with a polyfold structure `(F, M)`. -/
structure CategoryPolyfold : Type (u + 1) where
  /-- The GCT. -/
  C : GCT.{u}
  /-- The polyfold structure `(F, M)`. -/
  S : C.PolyfoldConstruction

end Polyfold
