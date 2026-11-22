import Polyfold.Chapter17.ProperCoveringStructure
import Polyfold.Chapter17.PolyfoldConstruction
import Polyfold.Chapter10.Equivalence

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17, §17.8
"Proper Covering Constructions": **Definition 17.8.10** (pp. 834–835, proper covering
uniformizer), **Remark 17.8.11** (p. 835), **Definition 17.8.12** (pp. 835–836, proper covering
uniformizer construction, the transition sets (17.101) and the map `p` of (17.102)) and
**Lemma 17.8.14** (pp. 836–837, the bijection (17.103)).  Numbers and pages are the 2021 text's.

# Proper covering uniformizers

## The text, paraphrased

(Definition 17.8.10) For a proper covering functor `P : A → B` of GCTs, a proper covering
uniformizer at `β` with isotropy `G = G_β` is a pair of functors `Ψ̂ : E → A`,
`Ψ : G ⋉ O_β → B`, with `τ̂ : E → G ⋉ O_β` a proper ep-groupoid covering model (Definition
17.8.4), such that (1) `Ψ(o_β) = β` and `Ψ̂` maps the distinguished points `o_α`, `α ∈ P⁻¹(β)`,
bijectively onto `P⁻¹(β)`; (2) `Ψ`, `Ψ̂` are fully faithful, injective on objects and
`P ∘ Ψ̂ = Ψ ∘ τ̂`; (3) on objects `P⁻¹(Ψ(O_β))` is the image of `Ψ̂`; (4) there is an open
neighbourhood `U` of `|β|` with `|Ψ| : |G ⋉ O_β| → U` and `|Ψ̂| : |E| → |P|⁻¹(U)` homeomorphisms.
(Remark 17.8.11) `Ψ` is a uniformizer in the usual sense; `Ψ̂` is not, but its restrictions to
`G_α ⋉ O_α` are.
(Definition 17.8.12) A proper covering uniformizer construction is a functor `F : B → SET`
assigning to `β` a set `F(β)` of proper covering uniformizers with `Ψ(o_β) = β`.  The transition
sets are `M(Ψ̂, Ψ̂') = {(e, φ, e') | φ ∈ mor(Ψ̂(e), Ψ̂'(e'))}` (17.101), `M(Ψ, Ψ')` as usual, and
`p(e, φ, e') = (τ̂(e), P(φ), τ̂'(e'))` (17.102).
(Lemma 17.8.14) `M(Ψ̂, Ψ̂') → M(Ψ, Ψ') ₛ×_τ̂ E`, `(e, φ, e') ↦ (p(e, φ, e'), e)`, is a
well-defined bijection.  *Proof*: injectivity from Definition 17.8.1 (4) and the injectivity of
`Ψ̂'` on objects; surjectivity by lifting `φ̃` with source `Ψ̂(e)` (Definition 17.8.1 (4)) and
Definition 17.8.10 (3).

## What is formalized

* **Definition 17.8.10**: `ProperCoveringUniformizer P β`, the uniformizer `Ψ` (a
  `Uniformizer` of `B`: fully faithful, injective on objects), the ep-groupoid `E`, the model
  `τ̂` (`ProperCoveringModel`), the functor `Ψ̂` (`hat`) and the conditions (1)–(4).
* **Remark 17.8.11** (first sentence): `toLocalUniformizer` (`Ψ` with (4) is a local uniformizer
  of Definition 17.1.3), `isCentredAt` (centred at `β`), `isotropy` (`G ≅ G_β`, "with isotropy
  `G = G_β`"), and `footprint_toLocalUniformizer`.
* **Definition 17.8.12**: `ProperCoveringUniformizerConstruction P` (the sets `F(β)`), the induced
  uniformizer construction of `B` (`toUniformizerConstruction`), the transition sets `HatTrans`
  (17.101) and the map `transMap` (17.102).
* **Lemma 17.8.14**: `lemma_17_8_14` (`fibredTransMap` is bijective), with the inverse
  `fibredTransInv`.
* Witnesses: `sheetUniformizer` (for a nonempty discrete `G`-set `S` of sheets and a `G`-fixed
  point, the identity `G ⋉ (S × O) → A` over the tautological uniformizer of `B = G ⋉ O`),
  `sheetConstruction` (all `G`-fixed points), and the non-degenerate instance
  `reflectionSheetUniformizer` (two sheets of `ℤˣ ⋉ ℝ` over `ℤˣ ⋉ ℝ`, `-1` acting by the
  reflection, at `0`; `reflectionSheetUniformizer_nondegenerate`), over the proper covering functor
  `isProperCoveringGCT_reflectionSheets`.

## Readings

* "A pair of functors `Ψ̂ : E → A`, `Ψ : G ⋉ O_β → B`": `Ψ` is a `Uniformizer` of `B` (Definition
  17.1.3 without the topological condition; its conditions are those of (2) for `Ψ`), and `Ψ̂` a
  functor of the underlying groupoids.  The ep-groupoid `E` has objects and morphisms in the
  universe of `A` and `B`.
* "With isotropy `G = G_β`" is a consequence: `G` fixes `o_β` (Definition 17.8.4) and `Ψ` is fully
  faithful, so `G ≅ G_β` (`isotropy`).
* "The distinguished points `o_α ∈ O_α`, `α ∈ P⁻¹(β)`" are the points of `τ̂⁻¹(o_β)` (the
  construction after Definition 17.8.3 has `O_α ∋ o_α` over `o_β`); (1) is
  `BijOn Ψ̂ τ̂⁻¹(o_β) P⁻¹(β)`.
* "Homeomorphism onto `U`, resp. `|P|⁻¹(U)`" in (4): an embedding with that range.
* Definition 17.8.12: the functor `F : B → SET` is read on objects, as for Definition 17.1.6
  (`GCT.UniformizerConstruction`); `F(β)` may be empty, as there.  `Ψ(o_β) = β` is part of
  `ProperCoveringUniformizer P β`.
* The fibred product `M(Ψ, Ψ') ₛ×_τ̂ E` of (17.103) is `{(a, e) | s(a) = τ̂(e)}`.
* The definitions do not use that `P` is a proper covering functor; Lemma 17.8.14 does
  (`P.IsProperCoveringGCT`).
-/

open Set Function Topology

noncomputable section

universe u

namespace Polyfold

open EpGroupoid EpGroupoid.Examples

variable {A B : GCT.{u}} (P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr)

/-! ### Definition 17.8.10 -/

/-- **Definition 17.8.10 (proper covering uniformizer)**, pp. 834–835: at the object `β` of `B`,
a pair of functors `Ψ̂ : E → A` (`hat`) and `Ψ : G ⋉ O_β → B` (`Ψ`), with
`τ̂ : E → G ⋉ O_β` a proper ep-groupoid covering model (Definition 17.8.4, `model`), such that
(1) `Ψ(o_β) = β` and `Ψ̂` maps `τ̂⁻¹(o_β)` bijectively onto `P⁻¹(β)`; (2) `Ψ` and `Ψ̂` are fully
faithful and injective on objects (for `Ψ`: the fields of `Uniformizer`) and `P ∘ Ψ̂ = Ψ ∘ τ̂`;
(3) `P⁻¹(Ψ(O_β)) = Ψ̂(E)` on objects; (4) an open neighbourhood `U` of `|β|` with
`|Ψ| : |G ⋉ O_β| → U` and `|Ψ̂| : |E| → |P|⁻¹(U)` homeomorphisms. -/
structure ProperCoveringUniformizer (β : B.Obj) : Type (u + 1) where
  /-- The functor `Ψ : G ⋉ O_β → B`. -/
  Ψ : B.toGroupoidalCategory.Uniformizer
  /-- The objects of `E`. -/
  ObjE : Type u
  /-- The morphisms of `E`. -/
  MorE : Type u
  [topObjE : TopologicalSpace ObjE]
  [t2ObjE : T2Space ObjE]
  [paraObjE : ParacompactSpace ObjE]
  [topMorE : TopologicalSpace MorE]
  [t2MorE : T2Space MorE]
  [paraMorE : ParacompactSpace MorE]
  /-- The ep-groupoid `E`. -/
  E : EpGroupoid ObjE MorE
  /-- The functor `τ̂ : E → G ⋉ O_β`. -/
  τ : EpFunctor E (actionEpGroupoid Ψ.smooth_smul)
  /-- `τ̂` is a proper covering model (Definition 17.8.4); its point is `o_β`. -/
  model : ProperCoveringModel τ
  /-- The functor `Ψ̂ : E → A`. -/
  hat : GroupoidFunctor E.toGroupoidStr A.toGroupoidStr
  /-- (1) `Ψ(o_β) = β`. -/
  obj_pt : Ψ.obj model.pt = β
  /-- (1) `Ψ̂` maps the distinguished points bijectively onto `P⁻¹(β)`. -/
  bijOn_fiber : BijOn hat.obj model.fiber (P.obj ⁻¹' {β})
  /-- (2) `Ψ̂` is injective on objects. -/
  injective_hat : Injective hat.obj
  /-- (2) `Ψ̂` is full. -/
  full_hat : hat.toFunctor.Full
  /-- (2) `Ψ̂` is faithful. -/
  faithful_hat : hat.toFunctor.Faithful
  /-- (2) `P ∘ Ψ̂ = Ψ ∘ τ̂` on objects. -/
  obj_comm : ∀ e, P.obj (hat.obj e) = Ψ.obj (τ.obj e)
  /-- (2) `P ∘ Ψ̂ = Ψ ∘ τ̂` on morphisms. -/
  mor_comm : ∀ φ, P.mor (hat.mor φ) = Ψ.mor (τ.mor φ)
  /-- (3) `P⁻¹(Ψ(O_β)) = Ψ̂(E)` on objects. -/
  preimage_range : P.obj ⁻¹' range Ψ.obj = range hat.obj
  /-- (4) `|Ψ|` and `|Ψ̂|` are homeomorphisms onto `U` and `|P|⁻¹(U)`. -/
  orbit_homeomorph : ∃ U : Set B.OrbitSpace, IsOpen U ∧ B.π β ∈ U ∧
    IsEmbedding Ψ.functor.orbitMap ∧ range Ψ.functor.orbitMap = U ∧
    IsEmbedding hat.orbitMap ∧ range hat.orbitMap = P.orbitMap ⁻¹' U

namespace ProperCoveringUniformizer

attribute [instance] topObjE t2ObjE paraObjE topMorE t2MorE paraMorE

variable {P} {β : B.Obj} (U : ProperCoveringUniformizer P β)

/-! ### Remark 17.8.11 -/

/-- **Remark 17.8.11**: `Ψ : G ⋉ O_β → B` is a uniformizer in the usual sense (Definition 17.1.3):
(4) makes `|Ψ|` an open embedding. -/
def toLocalUniformizer : B.LocalUniformizer :=
  { U.Ψ with
    isOpenEmbedding_orbitMap := by
      obtain ⟨V, hV, -, he, hr, -⟩ := U.orbit_homeomorph
      exact ⟨he, hr ▸ hV⟩ }

@[simp] theorem toLocalUniformizer_toUniformizer : U.toLocalUniformizer.toUniformizer = U.Ψ := rfl

/-- **Remark 17.8.11**: the uniformizer `Ψ` is centred at `β`: `Ψ(o_β) = β` with `o_β` fixed by
`G`. -/
theorem isCentredAt : U.Ψ.IsCentredAt β := ⟨U.model.pt, U.obj_pt, U.model.smul_pt⟩

theorem toLocalUniformizer_isAt : U.toLocalUniformizer.IsAt β := U.isCentredAt.isAt

/-- **Definition 17.8.10, "with isotropy `G = G_β`"**: `g ↦ Ψ(g, o_β)` is an isomorphism of `G` onto
the isotropy group of `β`. -/
def isotropy : U.Ψ.G ≃* B.toGroupoidStr.Isotropy (U.Ψ.obj U.model.pt) :=
  U.Ψ.isotropyEquiv U.model.smul_pt

/-- The footprint of `Ψ` is the open set `U` of (4), and `|P|⁻¹(U)` is the image of `|Ψ̂|`. -/
theorem footprint_toLocalUniformizer :
    B.π β ∈ U.toLocalUniformizer.footprint ∧
      range U.hat.orbitMap = P.orbitMap ⁻¹' U.toLocalUniformizer.footprint := by
  obtain ⟨V, -, hβ, -, hr, -, hr'⟩ := U.orbit_homeomorph
  have hf : U.toLocalUniformizer.footprint = V := hr
  rw [hf]
  exact ⟨hβ, hr'⟩

/-! ### The transition sets (17.101) and the map `p` (17.102) -/

variable {β' : B.Obj}

/-- **The transition set `M(Ψ̂, Ψ̂')`** of (17.101), p. 836: the triples `(e, φ, e')` with
`φ : Ψ̂(e) → Ψ̂'(e')` a morphism of `A`. -/
abbrev HatTrans (U : ProperCoveringUniformizer P β) (U' : ProperCoveringUniformizer P β') :
    Type u :=
  A.toGroupoidStr.TransitionSet U.hat.obj U'.hat.obj

/-- **The map `p : M(Ψ̂, Ψ̂') → M(Ψ, Ψ')`** of (17.101)–(17.102), p. 836:
`p(e, φ, e') = (τ̂(e), P(φ), τ̂'(e'))`; it is well defined because `P ∘ Ψ̂ = Ψ ∘ τ̂`. -/
def transMap (U : ProperCoveringUniformizer P β) (U' : ProperCoveringUniformizer P β')
    (a : HatTrans U U') : U.Ψ.Trans U'.Ψ where
  src := U.τ.obj a.src
  mor := P.mor a.mor
  tgt := U'.τ.obj a.tgt
  src_mor := by rw [P.src_mor, a.src_mor, U.obj_comm]
  tgt_mor := by rw [P.tgt_mor, a.tgt_mor, U'.obj_comm]

@[simp] theorem transMap_src (U' : ProperCoveringUniformizer P β') (a : HatTrans U U') :
    (transMap U U' a).src = U.τ.obj a.src := rfl

@[simp] theorem transMap_mor (U' : ProperCoveringUniformizer P β') (a : HatTrans U U') :
    (transMap U U' a).mor = P.mor a.mor := rfl

@[simp] theorem transMap_tgt (U' : ProperCoveringUniformizer P β') (a : HatTrans U U') :
    (transMap U U' a).tgt = U'.τ.obj a.tgt := rfl

/-! ### Lemma 17.8.14 -/

/-- The fibred product `M(Ψ, Ψ') ₛ×_τ̂ E = {(a, e) | s(a) = τ̂(e)}` of (17.103). -/
abbrev TransFibred (U : ProperCoveringUniformizer P β) (U' : ProperCoveringUniformizer P β') :
    Type u :=
  {q : U.Ψ.Trans U'.Ψ × U.ObjE // q.1.src = U.τ.obj q.2}

/-- **The map (17.103)**: `(e, φ, e') ↦ (p(e, φ, e'), e)`. -/
def fibredTransMap (U : ProperCoveringUniformizer P β) (U' : ProperCoveringUniformizer P β')
    (a : HatTrans U U') : TransFibred U U' :=
  ⟨(transMap U U' a, a.src), rfl⟩

@[simp] theorem fibredTransMap_fst (U' : ProperCoveringUniformizer P β') (a : HatTrans U U') :
    (fibredTransMap U U' a).1.1 = transMap U U' a := rfl

@[simp] theorem fibredTransMap_snd (U' : ProperCoveringUniformizer P β') (a : HatTrans U U') :
    (fibredTransMap U U' a).1.2 = a.src := rfl

variable (hPc : P.IsProperCoveringGCT)
include hPc

/-- The lift of `φ̃` with source `Ψ̂(e)` (Definition 17.8.1 (4)), used for surjectivity. -/
theorem exists_lift (q : {p : B.Mor × A.Obj // B.toGroupoidStr.src p.1 = P.obj p.2}) :
    ∃ φ : A.Mor, P.mor φ = q.1.1 ∧ A.toGroupoidStr.src φ = q.1.2 := by
  obtain ⟨φ, hφ⟩ := hPc.bijective_fibredMor.2 q
  exact ⟨φ, congrArg (fun r => r.1.1) hφ, congrArg (fun r => r.1.2) hφ⟩

theorem eq_of_mor_eq_of_src_eq {φ φ₁ : A.Mor} (hm : P.mor φ = P.mor φ₁)
    (hs : A.toGroupoidStr.src φ = A.toGroupoidStr.src φ₁) : φ = φ₁ :=
  hPc.bijective_fibredMor.1 (Subtype.ext (Prod.ext hm hs))

/-- `M(Ψ̂, Ψ̂') → M(Ψ, Ψ') ₛ×_τ̂ E` is injective (first half of the proof of Lemma 17.8.14). -/
theorem injective_fibredTransMap (U' : ProperCoveringUniformizer P β') :
    Injective (fibredTransMap U U') := by
  intro a a₁ h
  have he : a.src = a₁.src := congrArg (fun q => q.1.2) h
  have hm : P.mor a.mor = P.mor a₁.mor := congrArg (fun q => q.1.1.mor) h
  have hs : A.toGroupoidStr.src a.mor = A.toGroupoidStr.src a₁.mor := by
    rw [a.src_mor, a₁.src_mor, he]
  have hφ : a.mor = a₁.mor := eq_of_mor_eq_of_src_eq hPc hm hs
  have ht : a.tgt = a₁.tgt := U'.injective_hat (by rw [← a.tgt_mor, ← a₁.tgt_mor, hφ])
  exact GroupoidStr.TransitionSet.ext he hφ ht

/-- The preimage of `(ã, e)`: `(e, φ, e')` with `φ` the lift of `φ̃` at `Ψ̂(e)` and `e'` the unique
point with `Ψ̂'(e') = t(φ)` (second half of the proof of Lemma 17.8.14). -/
theorem exists_fibredTransMap_eq (U' : ProperCoveringUniformizer P β') (q : TransFibred U U') :
    ∃ a, fibredTransMap U U' a = q := by
  obtain ⟨⟨a', e⟩, hq⟩ := q
  change a'.src = U.τ.obj e at hq
  have hsrc : B.toGroupoidStr.src a'.mor = P.obj (U.hat.obj e) := by
    rw [a'.src_mor, U.obj_comm, hq]
  obtain ⟨φ, hφm, hφs⟩ := exists_lift hPc ⟨(a'.mor, U.hat.obj e), hsrc⟩
  have hPt : P.obj (A.toGroupoidStr.tgt φ) = U'.Ψ.obj a'.tgt := by
    rw [← P.tgt_mor, hφm, a'.tgt_mor]
  obtain ⟨e', he'⟩ : A.toGroupoidStr.tgt φ ∈ range U'.hat.obj := by
    rw [← U'.preimage_range]
    exact ⟨a'.tgt, hPt.symm⟩
  have hτ : U'.τ.obj e' = a'.tgt := U'.Ψ.injective_obj (by
    change U'.Ψ.obj _ = U'.Ψ.obj _
    rw [← U'.obj_comm, he', hPt])
  refine ⟨⟨e, φ, e', hφs, he'.symm⟩, Subtype.ext (Prod.ext ?_ rfl)⟩
  exact GroupoidStr.TransitionSet.ext hq.symm hφm hτ

/-- **Lemma 17.8.14**, pp. 836–837: for a proper covering functor `P` and proper covering
uniformizers `(Ψ̂, Ψ)`, `(Ψ̂', Ψ')`, the map
`M(Ψ̂, Ψ̂') → M(Ψ, Ψ') ₛ×_τ̂ E`, `(e, φ, e') ↦ ((τ̂(e), P(φ), τ̂'(e')), e)`, is a bijection. -/
theorem lemma_17_8_14 (U' : ProperCoveringUniformizer P β') :
    Bijective (fibredTransMap U U') :=
  ⟨injective_fibredTransMap U hPc U', exists_fibredTransMap_eq U hPc U'⟩

/-- The inverse of (17.103). -/
def fibredTransInv (U' : ProperCoveringUniformizer P β') : TransFibred U U' → HatTrans U U' :=
  fun q => (exists_fibredTransMap_eq U hPc U' q).choose

theorem fibredTransMap_inv (U' : ProperCoveringUniformizer P β') (q : TransFibred U U') :
    fibredTransMap U U' (fibredTransInv U hPc U' q) = q :=
  (exists_fibredTransMap_eq U hPc U' q).choose_spec

theorem fibredTransInv_map (U' : ProperCoveringUniformizer P β') (a : HatTrans U U') :
    fibredTransInv U hPc U' (fibredTransMap U U' a) = a :=
  injective_fibredTransMap U hPc U' (fibredTransMap_inv U hPc U' _)

end ProperCoveringUniformizer

/-! ### Definition 17.8.12 -/

/-- **Definition 17.8.12 (proper covering uniformizer construction)**, pp. 835–836: the sets
`F(β)` of proper covering uniformizers at `β` (with `Ψ(o_β) = β`, part of
`ProperCoveringUniformizer P β`).  As for Definition 17.1.6, the functor `F : B → SET` is read on
objects. -/
structure ProperCoveringUniformizerConstruction : Type (u + 1) where
  /-- The sets `F(β)`. -/
  F : (β : B.Obj) → Set (ProperCoveringUniformizer P β)

namespace ProperCoveringUniformizerConstruction

variable {P} (F : ProperCoveringUniformizerConstruction P)

/-- The proper covering uniformizers of the construction, `(β, (Ψ̂, Ψ))` with `(Ψ̂, Ψ) ∈ F(β)`. -/
def Unif : Type (u + 1) := {p : Σ β : B.Obj, ProperCoveringUniformizer P β // p.2 ∈ F.F p.1}

/-- The underlying proper covering uniformizer. -/
abbrev Unif.unif {F : ProperCoveringUniformizerConstruction P} (U : F.Unif) :
    ProperCoveringUniformizer P U.1.1 :=
  U.1.2

/-- **The induced uniformizer construction of `B`** (Definition 17.1.6; Remark 17.8.11): `F_B(β)`
consists of the uniformizers `Ψ` of the pairs `(Ψ̂, Ψ) ∈ F(β)`. -/
def toUniformizerConstruction : B.UniformizerConstruction where
  F β := (fun U => U.toLocalUniformizer) '' F.F β
  isAt β := by
    rintro _ ⟨U, -, rfl⟩
    exact U.toLocalUniformizer_isAt

theorem mem_toUniformizerConstruction {U : F.Unif} :
    U.unif.toLocalUniformizer ∈ F.toUniformizerConstruction.F U.1.1 :=
  ⟨U.unif, U.2, rfl⟩

end ProperCoveringUniformizerConstruction

/-! ### Witnesses: sheet uniformizers -/

section Sheet

variable {G : Type u} [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]
  {O : Type u} [TopologicalSpace O] [T2Space O] [ParacompactSpace O] [MulAction G O]
  {PO : MPolyfold O} (hP : ∀ g : G, PO.IsScSmoothMap PO fun y => g • y)
  (S : Type u) [TopologicalSpace S] [DiscreteTopology S] [MulAction G S]
  [ParacompactSpace (S × O)] [Nonempty S]

/-- **The sheet proper covering uniformizer** (Definition 17.8.10) at a `G`-fixed point `ō` of
`O`, for the sheet functor `P : G ⋉ (S × O) → G ⋉ O`: `Ψ` the tautological uniformizer of
`G ⋉ O`, `E = G ⋉ (S × O)` with the sheet model at `ō` (`sheetModel`), `Ψ̂` the identity, and
`U = |B|` in (4). -/
def sheetUniformizer (pt : O) (hpt : ∀ g : G, g • pt = pt) :
    ProperCoveringUniformizer (sheetGCTFunctor hP S) pt where
  Ψ := (GCT.LocalUniformizer.tautological PO hP).toUniformizer
  ObjE := S × O
  MorE := G × (S × O)
  E := sheetEp hP S
  τ := sheetFunctor hP S
  model := sheetModel hP S pt hpt
  hat := GroupoidFunctor.id _
  obj_pt := rfl
  bijOn_fiber := by
    have h : (sheetModel hP S pt hpt).fiber = (sheetGCTFunctor hP S).obj ⁻¹' {pt} := rfl
    rw [h]
    exact bijOn_id _
  injective_hat := injective_id
  full_hat := (GroupoidFunctor.full_iff _).2 fun _ _ ψ hs ht => ⟨ψ, hs, ht, rfl⟩
  faithful_hat := (GroupoidFunctor.faithful_iff _).2 fun _ _ _ _ h => h
  obj_comm _ := rfl
  mor_comm _ := rfl
  preimage_range := by
    have h1 : range (GCT.LocalUniformizer.tautological PO hP).toUniformizer.obj = univ :=
      range_id
    rw [h1, preimage_univ]
    exact range_id.symm
  orbit_homeomorph := by
    refine ⟨univ, isOpen_univ, mem_univ _, ?_, eq_univ_of_forall fun z => ?_, ?_, ?_⟩
    · change IsEmbedding (GroupoidFunctor.id (GroupoidStr.translation G O)).orbitMap
      rw [GCT.LocalUniformizer.orbitMap_id_eq]
      exact IsEmbedding.id
    · change z ∈ range (GroupoidFunctor.id (GroupoidStr.translation G O)).orbitMap
      rw [GCT.LocalUniformizer.orbitMap_id_eq]
      exact ⟨z, rfl⟩
    · change IsEmbedding (GroupoidFunctor.id (GroupoidStr.translation G (S × O))).orbitMap
      rw [GCT.LocalUniformizer.orbitMap_id_eq]
      exact IsEmbedding.id
    · rw [preimage_univ]
      change range (GroupoidFunctor.id (GroupoidStr.translation G (S × O))).orbitMap = univ
      rw [GCT.LocalUniformizer.orbitMap_id_eq]
      exact range_id

/-- **A proper covering uniformizer construction** (Definition 17.8.12) for the sheet functor: at
each `G`-fixed point the sheet uniformizer, and no uniformizer elsewhere. -/
def sheetConstruction : ProperCoveringUniformizerConstruction (sheetGCTFunctor hP S) where
  F β := {U | ∃ h : ∀ g : G, g • β = β, U = sheetUniformizer hP S β h}

theorem sheetUniformizer_mem (pt : O) (hpt : ∀ g : G, g • pt = pt) :
    sheetUniformizer hP S pt hpt ∈ (sheetConstruction hP S).F pt :=
  ⟨hpt, rfl⟩

/-- For a trivial action every `F(β)` of the sheet construction is nonempty. -/
theorem sheetConstruction_nonempty (htriv : ∀ (g : G) (x : O), g • x = x) (β : O) :
    ((sheetConstruction hP S).F β).Nonempty :=
  ⟨_, sheetUniformizer_mem hP S β (htriv · β)⟩

end Sheet

section Reflection

/-- `ℤˣ` acting trivially on the two sheets `Bool`. -/
local instance instMulActionUnitsBool' : MulAction ℤˣ Bool where
  smul _ b := b
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- **The non-degenerate witness of Definition 17.8.10**: two sheets of `ℤˣ ⋉ ℝ` over `ℤˣ ⋉ ℝ`, at
the fixed point `0`. -/
def reflectionSheetUniformizer :
    ProperCoveringUniformizer (sheetGCTFunctor isScSmoothMap_units_smul Bool)
      (0 : Fin 1 → ℝ) :=
  sheetUniformizer isScSmoothMap_units_smul Bool 0 units_smul_zero_rn

/-- The witness is non-degenerate: `P` is a proper covering functor of GCTs
(Definition 17.8.1), `τ̂⁻¹(o_β)` has two points, and `G = ℤˣ` acts nontrivially on `O = ℝ`. -/
theorem reflectionSheetUniformizer_nondegenerate :
    (sheetGCTFunctor isScSmoothMap_units_smul Bool).IsProperCoveringGCT ∧
      reflectionSheetUniformizer.model.fiber.ncard = 2 ∧
      ∃ (g : reflectionSheetUniformizer.Ψ.G) (x : reflectionSheetUniformizer.Ψ.O), g • x ≠ x := by
  refine ⟨isProperCoveringGCT_sheet isScSmoothMap_units_smul fun _ _ => rfl, ?_, ?_⟩
  · change (sheetModel isScSmoothMap_units_smul Bool 0 units_smul_zero_rn).fiber.ncard = 2
    rw [sheetModel_fiber]
    have : (univ ×ˢ {(0 : Fin 1 → ℝ)} : Set (Bool × (Fin 1 → ℝ))) = {(true, 0), (false, 0)} := by
      ext ⟨b, x⟩
      cases b <;> simp
    rw [this, ncard_pair (by simp)]
  · refine ⟨(-1 : ℤˣ), (fun _ => 1 : Fin 1 → ℝ), fun h => ?_⟩
    have := congrFun h 0
    change ((-1 : ℤˣ) • (fun _ => 1 : Fin 1 → ℝ)) 0 = 1 at this
    norm_num [Units.smul_def] at this

end Reflection

end Polyfold
