import Polyfold.Chapter8.TangentEp
import Polyfold.Chapter8.NatTrans
import Polyfold.Chapter8.SigmaPolyfold
import Polyfold.Chapter7.NonVacuity
import Polyfold.Chapter7.ReducedCriterion

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 10, "Equivalences and Localization", §10.1 "Equivalences" (pp. 461–477; 2017:
pp. 333–342): **Definition 10.1.1, Lemma 10.1.2, Definition 10.1.4, Propositions 10.1.5,
10.1.6, Theorem 10.1.7** (2017: Definitions 10.1, 10.2, Lemma 10.1, Propositions 10.2, 10.3,
Theorem 10.1).  Numbers and pages are the 2021 text's, the 2017 ones in parentheses.  The rest
of §10.1 is in `EquivalenceRefinement.lean` (Proposition 10.1.3), `EquivalenceReduced.lean`
(Remark 10.1.12, Propositions 10.1.13, 10.1.14, 10.1.16, 10.1.18), `EquivalenceZhou.lean`
(Proposition 10.1.17) and `EquivalenceExamples.lean` (Remark 10.1.11, Example 10.1.15).

# Equivalences of ep-groupoids

## The text, paraphrased

(p. 461) Besides the category `EP` of ep-groupoids and sc-smooth functors, the text mentions the
full subcategory `EP_lreg` of ep-groupoids with the local regularity property (Definition
7.4.19).  (Definition 10.1.1, p. 461 (2017: Definition 10.1, p. 333)) An equivalence
`F : X → Y` is an sc-smooth functor which (1) is faithful and full, (2) induces a homeomorphism
`|F| : |X| → |Y|`, (3) is a local sc-diffeomorphism on objects; the class of equivalences is
called `E`.  (pp. 461–462) Recollection of faithful, full, essentially surjective; for an
equivalence of categories `|F|` is a bijection.

(Lemma 10.1.2, p. 462 (2017: Lemma 10.1, p. 334)) An sc-smooth functor which is an equivalence
of categories and a local sc-diffeomorphism on objects is an equivalence.  *Proof* (text): `|F|`
is continuous, and open since `F` is open on objects and `π` is open.  (p. 462) Compositions of
equivalences are equivalences; an equivalence is in general not invertible as a functor.

(Definition 10.1.4, p. 463 (2017: Definition 10.2, p. 335)) `F, G : X → Y` are naturally
equivalent if there is an sc-smooth `τ : X → 𝐘` with `τ(x) : F(x) → G(x)` and
`G(φ) ∘ τ(x) = τ(x') ∘ F(φ)`.  (p. 464) `≃` is an equivalence relation, compatible with
composition on both sides.  (Proposition 10.1.5, p. 464 (2017: Proposition 10.2, p. 336),
quoted from the literature without proof) If `F ≃ G` and one of them is an equivalence, so is
the other.  (Proposition 10.1.6, p. 464 (2017: Proposition 10.3, p. 336)) If `F` and `Φ ∘ F`
are equivalences, so is `Φ`.  *Proof* (text): local diffeomorphism and essential surjectivity
pass to `Φ`, `|Φ| = |Φ ∘ F| ∘ |F|⁻¹`, and full faithfulness by conjugating with morphisms
`F(x) → y`.  (Theorem 10.1.7, p. 465 (2017: Theorem 10.1, p. 337)) The tangent `TF` of an
equivalence is an equivalence.  *Proof* (text): `TF` is a local sc-diffeomorphism; essential
surjectivity, fullness and faithfulness via `Tt ∘ (Ts)⁻¹`.

## What is formalized

* `EpFunctor.IsEquivalence` (**Definition 10.1.1**), `EP.equivalences` (the class `E`, a
  multiplicative `MorphismProperty` of `EP`); `GroupoidFunctor.full_iff`, `faithful_iff`,
  `essSurj_iff` (the category notions in terms of `src`, `tgt`, `mor`);
  `bijective_orbitMap_of_isEquivalence`.
* `EpFunctor.lemma_10_1_2` (**Lemma 10.1.2**), `isEquivalence_iff`; `IsEquivalence.id`,
  `IsEquivalence.comp`; consequences `IsEquivalence.exists_iso`, `exists_mor_eq`,
  `mor_injective`.
* `definition_10_1_4` (**Definition 10.1.4** and the claims after it), from the existing
  `EpNatTrans`, `EpFunctor.NaturallyEquivalent`, `naturallyEquivalent_equivalence`,
  `NaturallyEquivalent.comp_left`, `comp_right` (Definition 8.1.13); `EpNatTrans.toNatIso`.
* `EpFunctor.proposition_10_1_5` (**Proposition 10.1.5**), `proposition_10_1_6`
  (**Proposition 10.1.6**), `theorem_10_1_7` (**Theorem 10.1.7**).
* Local sc-diffeomorphisms at a point: `MPolyfold.IsLocalScDiffeoAt` with `comp`, `congr`,
  `of_comp_left`, `of_comp_right`; `EpFunctor.isLocalScDiffeoAt_mor`, `isLocalScDiffeo_mor`,
  `isLocalScDiffeoAt_obj_tgt`.
* Witnesses: `IsEquivalence.id`; `Examples.isEquivalence_pairToPoint` (the pair groupoid of `ℤ`
  to the point, a non-identity equivalence) with `not_exists_leftInverse_pairToPoint` (not
  invertible as a functor).

## What the text leaves implicit, and the choices made

* "Full and faithful" are Mathlib's `Functor.Full`, `Functor.Faithful` of the underlying functor
  `F.toFunctor` of the groupoids; "equivalence in the category sense" in Lemma 10.1.2 is
  Mathlib's `Functor.IsEquivalence`.  The orbit spaces carry the quotient topologies of
  Chapter 7; (2) is `IsHomeomorph F.orbitMap`.
* Proposition 10.1.6: the text's sentence on objects only covers the points `F(x)`; we add the
  transport along a morphism `F(x) → y` (`isLocalScDiffeoAt_obj_tgt`).  The proof writes
  `|Φ| : |X| → |Y|` for the map `|Y| → |Z|` (possible misprint).
* Not formalized here (G-items): the subcategory `EP_lreg` (not a numbered item); Remark 10.1.8
  (p. 467, new in the 2021 edition: Zhou's counterexample, which needs the weighted-Sobolev
  sc-retract of Appendix 10.6.3, not available in Lean); Proposition 10.1.9 (p. 468, new in the
  2021 edition: (LR) under equivalences, which needs a natural representation transported along
  `F` and `ψ : F(x) → y`, not provided by the `NaturalRep` API); Proposition 10.1.10 (p. 470
  (2017: Proposition 10.4, p. 340), which assumes (LR) and uses Proposition 10.1.9); Proposition
  10.1.19 (p. 477, new in the 2021 edition: (SLR), which rests on Proposition 10.1.9; its
  reduction to 10.1.9 is `EP.isSLR_iff_of_isLR_iff`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u v w

/-! ### Local sc-diffeomorphisms at a point -/

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}
  {Z : Type w} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {S : MPolyfold Z}

variable (P Q) in
/-- `f` is a **local sc-diffeomorphism at `x`**: an sc-diffeomorphism of an open neighbourhood of
`x` onto an open set.  `IsLocalScDiffeo` is this at every point (`isLocalScDiffeo_iff_forall`). -/
def IsLocalScDiffeoAt (f : X → Y) (x : X) : Prop :=
  ∃ (U : Set X) (V : Set Y) (g : Y → X), x ∈ U ∧ P.IsScDiffeoOn Q f g U V

theorem isLocalScDiffeo_iff_forall {f : X → Y} :
    P.IsLocalScDiffeo Q f ↔ ∀ x, P.IsLocalScDiffeoAt Q f x := Iff.rfl

theorem IsLocalScDiffeo.at {f : X → Y} (hf : P.IsLocalScDiffeo Q f) (x : X) :
    P.IsLocalScDiffeoAt Q f x := hf x

theorem IsScDiffeoOn.isLocalScDiffeoAt {f : X → Y} {g : Y → X} {U : Set X} {V : Set Y}
    (h : P.IsScDiffeoOn Q f g U V) {x : X} (hx : x ∈ U) : P.IsLocalScDiffeoAt Q f x :=
  ⟨U, V, g, hx, h⟩

/-- The composition of local sc-diffeomorphisms at `x` and at `f(x)`. -/
theorem IsLocalScDiffeoAt.comp {f : X → Y} {g : Y → Z} {x : X}
    (hg : Q.IsLocalScDiffeoAt S g (f x)) (hf : P.IsLocalScDiffeoAt Q f x) :
    P.IsLocalScDiffeoAt S (g ∘ f) x := by
  obtain ⟨U₁, V₁, h₁, hx, hd₁⟩ := hf
  obtain ⟨U₂, V₂, h₂, hfx, hd₂⟩ := hg
  have hU : IsOpen (U₁ ∩ f ⁻¹' U₂) :=
    hd₁.isScSmoothOn.continuousOn.isOpen_inter_preimage hd₁.isOpen_source hd₂.isOpen_source
  have e₁ := hd₁.restrict hU inter_subset_left
  have hsub : V₁ ∩ h₁ ⁻¹' (U₁ ∩ f ⁻¹' U₂) ⊆ U₂ := fun y hy => by
    have := hy.2.2
    rwa [mem_preimage, hd₁.right_inv y hy.1] at this
  exact ⟨U₁ ∩ f ⁻¹' U₂, _, h₁ ∘ h₂, ⟨hx, hfx⟩, (hd₂.restrict e₁.isOpen_target hsub).comp e₁⟩

/-- Being a local sc-diffeomorphism at `x` depends only on the germ at `x`. -/
theorem IsLocalScDiffeoAt.congr {f f' : X → Y} {x : X} (hf : P.IsLocalScDiffeoAt Q f x)
    (h : f =ᶠ[𝓝 x] f') : P.IsLocalScDiffeoAt Q f' x := by
  obtain ⟨U, V, g, hx, hd⟩ := hf
  obtain ⟨W, hWsub, hWo, hxW⟩ := mem_nhds_iff.1 h
  have hUW : IsOpen (U ∩ W) := hd.isOpen_source.inter hWo
  exact ⟨U ∩ W, _, g, ⟨hx, hxW⟩,
    (hd.restrict hUW inter_subset_left).congr fun y hy => hWsub hy.2⟩

/-- If `s` is a local sc-diffeomorphism at `τ(x)` and `s ∘ τ` one at `x`, then so is the
continuous `τ` (near `x`, `τ = (s|W)⁻¹ ∘ (s ∘ τ)`). -/
theorem IsLocalScDiffeoAt.of_comp_left {s : Y → Z} {τ : X → Y} {x : X}
    (hs : Q.IsLocalScDiffeoAt S s (τ x)) (hτ : Continuous τ)
    (h : P.IsLocalScDiffeoAt S (s ∘ τ) x) : P.IsLocalScDiffeoAt Q τ x := by
  obtain ⟨W, V, σ, hxW, hd⟩ := hs
  have h1 : S.IsLocalScDiffeoAt Q σ ((s ∘ τ) x) := hd.symm.isLocalScDiffeoAt (hd.mapsTo hxW)
  refine (h1.comp h).congr ?_
  filter_upwards [hτ.continuousAt.preimage_mem_nhds (hd.isOpen_source.mem_nhds hxW)] with z hz
  exact hd.left_inv _ hz

/-- If `f` is a local sc-diffeomorphism at `x` and `g ∘ f` one at `x`, then `g` is one at `f(x)`
(near `f(x)`, `g = (g ∘ f) ∘ (f|U)⁻¹`). -/
theorem IsLocalScDiffeoAt.of_comp_right {f : X → Y} {g : Y → Z} {x : X}
    (hf : P.IsLocalScDiffeoAt Q f x) (h : P.IsLocalScDiffeoAt S (g ∘ f) x) :
    Q.IsLocalScDiffeoAt S g (f x) := by
  obtain ⟨U, V, k, hxU, hd⟩ := hf
  have hk : Q.IsLocalScDiffeoAt P k (f x) := hd.symm.isLocalScDiffeoAt (hd.mapsTo hxU)
  have h' : P.IsLocalScDiffeoAt S (g ∘ f) (k (f x)) := by rw [hd.left_inv x hxU]; exact h
  refine (h'.comp hk).congr ?_
  filter_upwards [hd.isOpen_target.mem_nhds (hd.mapsTo hxU)] with z hz
  simp only [Function.comp_apply, hd.right_inv z hz]

end MPolyfold

/-! ### Full, faithful and essentially surjective functors in terms of the structure maps -/

namespace GroupoidFunctor

variable {Obj Mor : Type u} {Obj' Mor' : Type v} {G : GroupoidStr Obj Mor}
  {H : GroupoidStr Obj' Mor'} (F : GroupoidFunctor G H)

/-- `F` is **full**: every `ψ : F(x) → F(x')` is `F(φ)` for some `φ : x → x'`. -/
theorem full_iff : F.toFunctor.Full ↔ ∀ (x x' : Obj) (ψ : Mor'), H.src ψ = F.obj x →
    H.tgt ψ = F.obj x' → ∃ φ, G.src φ = x ∧ G.tgt φ = x' ∧ F.mor φ = ψ := by
  constructor
  · intro h x x' ψ hs ht
    obtain ⟨f, hf⟩ := h.map_surjective (X := G.toOb x) (Y := G.toOb x') (H.homMk ψ hs ht)
    exact ⟨f.1, f.2.1, f.2.2, congrArg Subtype.val hf⟩
  · intro h
    refine ⟨fun {x x'} ψ => ?_⟩
    obtain ⟨φ, hs, ht, he⟩ := h x x' ψ.1 ψ.2.1 ψ.2.2
    exact ⟨G.homMk φ hs ht, Subtype.ext he⟩

/-- `F` is **faithful**: `F` is injective on every `mor(x, x')`. -/
theorem faithful_iff : F.toFunctor.Faithful ↔ ∀ φ φ' : Mor, G.src φ = G.src φ' →
    G.tgt φ = G.tgt φ' → F.mor φ = F.mor φ' → φ = φ' := by
  constructor
  · intro h φ φ' hs ht he
    have := h.map_injective (X := G.toOb (G.src φ)) (Y := G.toOb (G.tgt φ))
      (a₁ := G.homMk φ rfl rfl) (a₂ := G.homMk φ' hs.symm ht.symm) (Subtype.ext he)
    exact congrArg Subtype.val this
  · intro h
    exact ⟨fun {_ _} f f' he => Subtype.ext (h f.1 f'.1 (f.2.1.trans f'.2.1.symm)
      (f.2.2.trans f'.2.2.symm) (congrArg Subtype.val he))⟩

/-- `F` is **essentially surjective**: every `y` is isomorphic to some `F(x)`. -/
theorem essSurj_iff : F.toFunctor.EssSurj ↔
    ∀ y : Obj', ∃ (x : Obj) (ψ : Mor'), H.src ψ = F.obj x ∧ H.tgt ψ = y := by
  constructor
  · intro h y
    obtain ⟨x, ⟨i⟩⟩ := Functor.EssSurj.mem_essImage F.toFunctor (H.toOb y)
    exact ⟨x, i.hom.1, i.hom.2.1, i.hom.2.2⟩
  · intro h
    refine ⟨fun y => ?_⟩
    obtain ⟨x, ψ, hs, ht⟩ := h y
    exact ⟨x, ⟨(Groupoid.isoEquivHom (H.toOb (F.obj x)) (H.toOb y)).symm (H.homMk ψ hs ht)⟩⟩

theorem toFunctor_comp {Obj'' Mor'' : Type w} {K : GroupoidStr Obj'' Mor''}
    (F' : GroupoidFunctor H K) : (F'.comp F).toFunctor = F.toFunctor ⋙ F'.toFunctor :=
  rfl

/-- If `F` is full, `|F|` is injective. -/
theorem injective_orbitMap_of_full (hF : F.toFunctor.Full) : Injective F.orbitMap := by
  intro a b hab
  induction a using Quotient.inductionOn with | h x => ?_
  induction b using Quotient.inductionOn with | h x' => ?_
  change H.π (F.obj x) = H.π (F.obj x') at hab
  obtain ⟨ψ, hs, ht⟩ := H.π_eq_π_iff.1 hab
  obtain ⟨φ, hφs, hφt, -⟩ := (F.full_iff.1 hF) x x' ψ hs ht
  exact G.π_eq_π_iff.2 ⟨φ, hφs, hφt⟩

/-- `|F|` is surjective iff `F` is essentially surjective. -/
theorem surjective_orbitMap_iff : Surjective F.orbitMap ↔ F.toFunctor.EssSurj := by
  rw [essSurj_iff]
  constructor
  · intro h y
    obtain ⟨a, ha⟩ := h (H.π y)
    induction a using Quotient.inductionOn with | h x => ?_
    obtain ⟨ψ, hs, ht⟩ := H.π_eq_π_iff.1 ha
    exact ⟨x, ψ, hs, ht⟩
  · intro h b
    induction b using Quotient.inductionOn with | h y => ?_
    obtain ⟨x, ψ, hs, ht⟩ := h y
    exact ⟨G.π x, H.π_eq_π_iff.2 ⟨ψ, hs, ht⟩⟩

/-- **The remark before Lemma 10.1.2**: for an equivalence of categories `|F|` is a bijection. -/
theorem bijective_orbitMap_of_isEquivalence (hF : F.toFunctor.IsEquivalence) :
    Bijective F.orbitMap :=
  ⟨F.injective_orbitMap_of_full hF.full, F.surjective_orbitMap_iff.2 hF.essSurj⟩

end GroupoidFunctor

/-! ### Definition 10.1.1 -/

section Equiv

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {Obj'' Mor'' : Type w} [TopologicalSpace Obj''] [T2Space Obj''] [ParacompactSpace Obj'']
  [TopologicalSpace Mor''] [T2Space Mor''] [ParacompactSpace Mor'']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {Z : EpGroupoid Obj'' Mor''}

namespace EpFunctor

/-- **2021 Definition 10.1.1, p. 461 (2017: Definition 10.1, p. 333)**: an **equivalence**
`F : X → Y` of ep-groupoids is an sc-smooth functor which (1) is full and faithful, (2) induces a
homeomorphism `|F| : |X| → |Y|` of the orbit spaces, and (3) is a local sc-diffeomorphism on
objects.  Witnesses: `IsEquivalence.id`, `Examples.isEquivalence_pairToPoint`. -/
structure IsEquivalence (F : EpFunctor X Y) : Prop where
  full : F.toFunctor.Full
  faithful : F.toFunctor.Faithful
  isHomeomorph_orbitMap : IsHomeomorph F.orbitMap
  isLocalScDiffeo_obj : X.PObj.IsLocalScDiffeo Y.PObj F.obj

theorem continuous_obj' (F : EpFunctor X Y) : Continuous F.obj :=
  continuousOn_univ.1 F.isScSmoothMap_obj.continuousOn

/-- `|F|` is continuous (the orbit spaces carry the quotient topologies). -/
theorem continuous_orbitMap (F : EpFunctor X Y) : Continuous F.orbitMap :=
  X.proposition_7_1_8_isOpenQuotientMap.isQuotientMap.continuous_iff.2
    (Y.continuous_π.comp F.continuous_obj')

/-- If `F` is open on objects, `|F|` is open (`π` is open, Proposition 7.1.8 of the text,
`proposition_7_1_8`). -/
theorem isOpenMap_orbitMap (F : EpFunctor X Y) (h : IsOpenMap F.obj) :
    IsOpenMap F.orbitMap := by
  intro O hO
  have he : F.orbitMap '' O = Y.π '' (F.obj '' (X.π ⁻¹' O)) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨x, rfl⟩ := X.surjective_π w
      exact ⟨F.obj x, ⟨x, hw, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨X.π x, hx, rfl⟩
  rw [he]
  exact Y.proposition_7_1_8 _ (h _ (hO.preimage X.continuous_π))

/-- **2021 Lemma 10.1.2, p. 462 (2017: Lemma 10.1, p. 334)**: an sc-smooth functor which is an
equivalence of categories (Mathlib's `Functor.IsEquivalence` of the underlying functor: full,
faithful, essentially surjective) and a local sc-diffeomorphism on objects is an equivalence in
the sense of Definition 10.1.1. -/
theorem lemma_10_1_2 (F : EpFunctor X Y) (hF : F.toFunctor.IsEquivalence)
    (h : X.PObj.IsLocalScDiffeo Y.PObj F.obj) : F.IsEquivalence where
  full := hF.full
  faithful := hF.faithful
  isHomeomorph_orbitMap := ⟨F.continuous_orbitMap, F.isOpenMap_orbitMap h.isOpenMap,
    F.bijective_orbitMap_of_isEquivalence hF⟩
  isLocalScDiffeo_obj := h

namespace IsEquivalence

variable {F : EpFunctor X Y} (hF : F.IsEquivalence)
include hF

/-- An equivalence is essentially surjective. -/
theorem essSurj : F.toFunctor.EssSurj :=
  F.surjective_orbitMap_iff.1 hF.isHomeomorph_orbitMap.surjective

/-- An equivalence is an equivalence of categories. -/
theorem isEquivalence_toFunctor : F.toFunctor.IsEquivalence :=
  { faithful := hF.faithful, full := hF.full, essSurj := hF.essSurj }

/-- Every object of `Y` is isomorphic to some `F(x)`. -/
theorem exists_iso (y : Obj') : ∃ (x : Obj) (ψ : Mor'), Y.src ψ = F.obj x ∧ Y.tgt ψ = y :=
  (F.essSurj_iff.1 hF.essSurj) y

/-- `F` is full, in terms of the structure maps. -/
theorem exists_mor_eq {x x' : Obj} {ψ : Mor'} (hs : Y.src ψ = F.obj x)
    (ht : Y.tgt ψ = F.obj x') : ∃ φ, X.src φ = x ∧ X.tgt φ = x' ∧ F.mor φ = ψ :=
  (F.full_iff.1 hF.full) x x' ψ hs ht

/-- `F` is faithful, in terms of the structure maps. -/
theorem mor_injective {φ φ' : Mor} (hs : X.src φ = X.src φ') (ht : X.tgt φ = X.tgt φ')
    (he : F.mor φ = F.mor φ') : φ = φ' :=
  (F.faithful_iff.1 hF.faithful) φ φ' hs ht he

end IsEquivalence

/-- **Definition 10.1.1 and Lemma 10.1.2 together**: `F` is an equivalence iff it is an
equivalence of categories and a local sc-diffeomorphism on objects. -/
theorem isEquivalence_iff (F : EpFunctor X Y) : F.IsEquivalence ↔
    F.toFunctor.IsEquivalence ∧ X.PObj.IsLocalScDiffeo Y.PObj F.obj :=
  ⟨fun h => ⟨h.isEquivalence_toFunctor, h.isLocalScDiffeo_obj⟩,
    fun h => F.lemma_10_1_2 h.1 h.2⟩

variable (X) in
/-- **The identity functor is an equivalence.** -/
theorem IsEquivalence.id : (EpFunctor.id X).IsEquivalence :=
  (EpFunctor.id X).lemma_10_1_2
    { faithful := (GroupoidFunctor.faithful_iff _).2 fun _ _ _ _ h => h
      full := (GroupoidFunctor.full_iff _).2 fun _ _ ψ hs ht => ⟨ψ, hs, ht, rfl⟩
      essSurj := (GroupoidFunctor.essSurj_iff _).2 fun y => ⟨y, X.unit y, X.src_unit y,
        X.tgt_unit y⟩ }
    MPolyfold.isLocalScDiffeo_id

/-- **The composition of equivalences is an equivalence** (2021 p. 462, after Lemma 10.1.2). -/
theorem IsEquivalence.comp {G : EpFunctor Y Z} {F : EpFunctor X Y} (hG : G.IsEquivalence)
    (hF : F.IsEquivalence) : (G.comp F).IsEquivalence := by
  rw [isEquivalence_iff] at hG hF ⊢
  have := hG.1
  have := hF.1
  refine ⟨?_, hG.2.comp hF.2⟩
  change (F.toFunctor ⋙ G.toFunctor).IsEquivalence
  infer_instance

end EpFunctor

/-- **The class `E` of equivalences** (2021 Definition 10.1.1), as a property of the morphisms of
the category `EP`; it contains the identities and is closed under composition. -/
def EP.equivalences : MorphismProperty EP.{u} := fun _ _ F => EpFunctor.IsEquivalence F

instance : EP.equivalences.{u}.IsMultiplicative where
  id_mem A := EpFunctor.IsEquivalence.id A.X
  comp_mem _ _ hF hG := EpFunctor.IsEquivalence.comp hG hF

/-! ### Local sc-diffeomorphisms along morphisms -/

namespace EpFunctor

variable (F : EpFunctor X Y)

/-- If `F` is a local sc-diffeomorphism on objects at `s(φ)`, then `F` on morphisms is one at
`φ` (`s_Y ∘ F = F ∘ s_X`, with `s_X`, `s_Y` local sc-diffeomorphisms). -/
theorem isLocalScDiffeoAt_mor {φ : Mor} (h : X.PObj.IsLocalScDiffeoAt Y.PObj F.obj (X.src φ)) :
    X.PMor.IsLocalScDiffeoAt Y.PMor F.mor φ := by
  have h1 : X.PMor.IsLocalScDiffeoAt Y.PObj (Y.src ∘ F.mor) φ :=
    (MPolyfold.IsLocalScDiffeoAt.comp h (X.isLocalScDiffeo_src.at φ)).congr
      (Eventually.of_forall fun z => (F.src_mor z).symm)
  exact MPolyfold.IsLocalScDiffeoAt.of_comp_left (Y.isLocalScDiffeo_src.at (F.mor φ))
    F.continuous_mor h1

/-- A functor which is a local sc-diffeomorphism on objects is one on morphisms. -/
theorem isLocalScDiffeo_mor (h : X.PObj.IsLocalScDiffeo Y.PObj F.obj) :
    X.PMor.IsLocalScDiffeo Y.PMor F.mor := fun _ => F.isLocalScDiffeoAt_mor (h.at _)

/-- **Transport along a morphism**: if `F` is a local sc-diffeomorphism on objects at `s(φ)`,
it is one at `t(φ)` (`F ∘ t_X = t_Y ∘ F` near `φ`). -/
theorem isLocalScDiffeoAt_obj_tgt {φ : Mor}
    (h : X.PObj.IsLocalScDiffeoAt Y.PObj F.obj (X.src φ)) :
    X.PObj.IsLocalScDiffeoAt Y.PObj F.obj (X.tgt φ) := by
  have h1 : X.PMor.IsLocalScDiffeoAt Y.PObj (F.obj ∘ X.tgt) φ :=
    (MPolyfold.IsLocalScDiffeoAt.comp (Y.isLocalScDiffeo_tgt.at (F.mor φ))
      (F.isLocalScDiffeoAt_mor h)).congr (Eventually.of_forall fun z => F.tgt_mor z)
  exact MPolyfold.IsLocalScDiffeoAt.of_comp_right (X.isLocalScDiffeo_tgt.at φ) h1

end EpFunctor

/-! ### Definition 10.1.4: natural equivalence -/

/-- **2021 Definition 10.1.4, p. 463 (2017: Definition 10.2, p. 335)**: natural equivalence of
sc-smooth functors is Definition 8.1.13 (`EpNatTrans`, `EpFunctor.NaturallyEquivalent`, the
naturality `τ(x') ∘ F(φ) = G(φ) ∘ τ(x)` being `EpNatTrans.naturality`).  The claims after it
(p. 464): `≃` is an equivalence relation, and `F ≃ G` implies `F ∘ Ψ ≃ G ∘ Ψ` and
`Φ ∘ F ≃ Φ ∘ G`. -/
theorem definition_10_1_4 :
    Equivalence (EpFunctor.NaturallyEquivalent (X := X) (Y := Y)) ∧
      (∀ {F G : EpFunctor X Y}, F.NaturallyEquivalent G →
        ∀ Ψ : EpFunctor Z X, (F.comp Ψ).NaturallyEquivalent (G.comp Ψ)) ∧
      (∀ {F G : EpFunctor X Y}, F.NaturallyEquivalent G →
        ∀ Φ : EpFunctor Y Z, (Φ.comp F).NaturallyEquivalent (Φ.comp G)) :=
  ⟨EpFunctor.naturallyEquivalent_equivalence, fun h Ψ => h.comp_left Ψ,
    fun h Φ => h.comp_right Φ⟩

/-! ### Proposition 10.1.5 -/

namespace EpNatTrans

variable {F G : EpFunctor X Y}

/-- A natural transformation `τ : F → G` of sc-smooth functors is a natural isomorphism of the
underlying functors (all morphisms of a groupoid are invertible). -/
def toNatIso (τ : EpNatTrans F G) : F.toFunctor ≅ G.toFunctor :=
  NatIso.ofComponents
    (fun x => (Groupoid.isoEquivHom (F.toFunctor.obj x) (G.toFunctor.obj x)).symm
      (Y.homMk (τ.app x) (τ.src_app x) (τ.tgt_app x)))
    (fun {x x'} f => by
      obtain ⟨φ, rfl, rfl⟩ := f
      exact GroupoidStr.Ob.hom_ext (τ.naturality φ))

theorem continuous_app (τ : EpNatTrans F G) : Continuous τ.app :=
  continuousOn_univ.1 τ.isScSmoothMap_app.continuousOn

/-- `τ` is a local sc-diffeomorphism `X → 𝐘` if `F` is one on objects (`s_Y ∘ τ = F`). -/
theorem isLocalScDiffeo_app (τ : EpNatTrans F G) (h : X.PObj.IsLocalScDiffeo Y.PObj F.obj) :
    X.PObj.IsLocalScDiffeo Y.PMor τ.app := fun x =>
  MPolyfold.IsLocalScDiffeoAt.of_comp_left (Y.isLocalScDiffeo_src.at (τ.app x)) τ.continuous_app
    ((h.at x).congr (Eventually.of_forall fun z => (τ.src_app z).symm))

/-- If `F` is a local sc-diffeomorphism on objects, so is `G = t_Y ∘ τ`. -/
theorem isLocalScDiffeo_obj (τ : EpNatTrans F G) (h : X.PObj.IsLocalScDiffeo Y.PObj F.obj) :
    X.PObj.IsLocalScDiffeo Y.PObj G.obj := fun x =>
  (MPolyfold.IsLocalScDiffeoAt.comp (Y.isLocalScDiffeo_tgt.at (τ.app x))
    ((τ.isLocalScDiffeo_app h).at x)).congr (Eventually.of_forall fun z => τ.tgt_app z)

end EpNatTrans

namespace EpFunctor

theorem IsEquivalence.of_natTrans {F G : EpFunctor X Y} (τ : EpNatTrans F G)
    (hF : F.IsEquivalence) : G.IsEquivalence := by
  rw [isEquivalence_iff] at hF ⊢
  have := hF.1
  exact ⟨Functor.isEquivalence_of_iso τ.toNatIso, τ.isLocalScDiffeo_obj hF.2⟩

/-- **2021 Proposition 10.1.5, p. 464 (2017: Proposition 10.2, p. 336)**: if `F ≃ G`, then `F`
is an equivalence iff `G` is one. -/
theorem proposition_10_1_5 {F G : EpFunctor X Y} (h : F.NaturallyEquivalent G) :
    F.IsEquivalence ↔ G.IsEquivalence := by
  obtain ⟨τ⟩ := h
  exact ⟨IsEquivalence.of_natTrans τ, IsEquivalence.of_natTrans τ.symm⟩

/-! ### Proposition 10.1.6 -/

/-- **2021 Proposition 10.1.6, p. 464 (2017: Proposition 10.3, p. 336)**: if `F : X → Y` and
`Φ ∘ F : X → Z` are equivalences, so is the sc-smooth functor `Φ : Y → Z`.  (On objects: `Φ` is
a local sc-diffeomorphism at the points `F(x)` (`F` and `Φ ∘ F` are), and at every `y` by
transport along a morphism `F(x) → y`, `isLocalScDiffeoAt_obj_tgt`.) -/
theorem proposition_10_1_6 {F : EpFunctor X Y} {Φ : EpFunctor Y Z} (hF : F.IsEquivalence)
    (hΦF : (Φ.comp F).IsEquivalence) : Φ.IsEquivalence := by
  obtain ⟨hFc, hFd⟩ := (isEquivalence_iff F).1 hF
  obtain ⟨hΦFc, hΦFd⟩ := (isEquivalence_iff _).1 hΦF
  have := hFc
  have : (F.toFunctor ⋙ Φ.toFunctor).IsEquivalence := hΦFc
  refine Φ.lemma_10_1_2 (Functor.isEquivalence_of_comp_left F.toFunctor Φ.toFunctor)
    fun y => ?_
  obtain ⟨x, ψ, hs, ht⟩ := hF.exists_iso y
  have h1 : Y.PObj.IsLocalScDiffeoAt Z.PObj Φ.obj (F.obj x) :=
    MPolyfold.IsLocalScDiffeoAt.of_comp_right (hFd.at x) (hΦFd.at x)
  rw [← ht]
  exact Φ.isLocalScDiffeoAt_obj_tgt (hs ▸ h1)

/-! ### Theorem 10.1.7 -/

/-- **2021 Theorem 10.1.7, p. 465 (2017: Theorem 10.1, p. 337)**: the tangent
`TF : TX → TY` of an equivalence is an equivalence. -/
theorem theorem_10_1_7 {F : EpFunctor X Y} (hF : F.IsEquivalence) : F.tangent.IsEquivalence := by
  have hd := hF.isLocalScDiffeo_obj
  have hTF : ∀ a, Y.tSrc (F.tangent.mor a) = F.tangent.obj (X.tSrc a) := F.tangent.src_mor
  have hTF' : ∀ a, Y.tTgt (F.tangent.mor a) = F.tangent.obj (X.tTgt a) := F.tangent.tgt_mor
  have hbase : ∀ a, Y.PObj.levelVal 1 (Y.PObj.tangentProj (F.tangent.obj a)) =
      F.obj (X.PObj.levelVal 1 (X.PObj.tangentProj a)) := fun a =>
    MPolyfold.levelVal_tangentProj_tangentMap F.isScSmoothMap_obj a
  have hmor : ∀ v, Y.tBase (F.tangent.mor v) = F.mor (X.tBase v) := fun v =>
    Y.tBase_tangentMap F.isScSmoothMap_mor v
  refine F.tangent.lemma_10_1_2
    { faithful := (GroupoidFunctor.faithful_iff _).2 fun v v' hs ht he => ?_
      full := (GroupoidFunctor.full_iff _).2 fun a a' k hs ht => ?_
      essSurj := (GroupoidFunctor.essSurj_iff _).2 fun b => ?_ } hd.tangentMap
  · -- faithful
    change X.tSrc v = X.tSrc v' at hs
    change X.tTgt v = X.tTgt v' at ht
    change F.tangent.mor v = F.tangent.mor v' at he
    have hb : X.tBase v = X.tBase v' := by
      refine hF.mor_injective ?_ ?_ ?_
      · rw [← X.levelVal_tangentProj_tSrc, ← X.levelVal_tangentProj_tSrc, hs]
      · rw [← X.levelVal_tangentProj_tTgt, ← X.levelVal_tangentProj_tTgt, ht]
      · rw [← hmor, ← hmor, he]
    exact X.tangent_ext hb hs
  · -- full
    change Y.tSrc k = F.tangent.obj a at hs
    change Y.tTgt k = F.tangent.obj a' at ht
    have hks : Y.src (Y.tBase k) = F.obj (X.PObj.levelVal 1 (X.PObj.tangentProj a)) := by
      rw [← Y.levelVal_tangentProj_tSrc, hs, hbase]
    have hkt : Y.tgt (Y.tBase k) = F.obj (X.PObj.levelVal 1 (X.PObj.tangentProj a')) := by
      rw [← Y.levelVal_tangentProj_tTgt, ht, hbase]
    obtain ⟨φ, hφs, hφt, hφ⟩ := hF.exists_mor_eq hks hkt
    have hφ1 : φ ∈ X.PMor.levelSet 1 :=
      (X.mem_levelSet_src_iff φ 1).1 (hφs ▸ MPolyfold.levelVal_mem _)
    obtain ⟨h, hhb, hhs⟩ := X.exists_tSrc_eq' hφ1 (a := a) hφs.symm
    have hk : F.tangent.mor h = k := by
      refine Y.tangent_ext ?_ ?_
      · rw [hmor, hhb, hφ]
      · rw [hTF, hhs, hs]
    have hht : X.tTgt h = a' := by
      have hfib : X.PObj.tangentProj (X.tTgt h) = X.PObj.tangentProj a' :=
        MPolyfold.level_ext (by rw [X.levelVal_tangentProj_tTgt, hhb, hφt])
      refine hd.injOn_tangentFiber (X.PObj.tangentProj a') hfib rfl ?_
      change F.tangent.obj (X.tTgt h) = F.tangent.obj a'
      rw [← hTF', hk, ht]
    exact ⟨h, hhs, hht, hk⟩
  · -- essentially surjective
    obtain ⟨x, ψ, hs, ht⟩ := hF.exists_iso (Y.PObj.levelVal 1 (Y.PObj.tangentProj b))
    have hψ1 : Y.inv ψ ∈ Y.PMor.levelSet 1 :=
      (Y.mem_levelSet_src_iff _ 1).1 (by rw [Y.src_inv, ht]; exact MPolyfold.levelVal_mem _)
    obtain ⟨k', hk'b, hk's⟩ := Y.exists_tSrc_eq' hψ1 (a := b) (by rw [Y.src_inv, ht])
    have hx1 : x ∈ X.PObj.levelSet 1 := by
      have : F.obj x ∈ Y.PObj.levelSet 1 := by
        rw [← hs, ← Y.tgt_inv, ← hk'b, ← Y.levelVal_tangentProj_tTgt]
        exact MPolyfold.levelVal_mem _
      exact (hd.mem_levelSet_iff x 1).1 this
    have hxy : F.obj (X.PObj.levelVal 1 (X.PObj.levelMk 1 x hx1)) =
        Y.PObj.levelVal 1 (Y.PObj.tangentProj (Y.tTgt k')) := by
      rw [MPolyfold.levelVal_levelMk, Y.levelVal_tangentProj_tTgt, hk'b, Y.tgt_inv, hs]
    obtain ⟨a, -, ha⟩ := hd.tangentFiber_subset_image (X.PObj.levelMk 1 x hx1) _ hxy
      (show Y.tTgt k' ∈ Y.PObj.tangentFiber _ from rfl)
    refine ⟨a, Y.tInv k', ?_, ?_⟩
    · change Y.tSrc (Y.tInv k') = F.tangent.obj a
      rw [Y.tSrc_tInv]
      exact ha.symm
    · change Y.tTgt (Y.tInv k') = b
      rw [Y.tTgt_tInv, hk's]

end EpFunctor

end Equiv

/-! ### Witnesses: a non-identity equivalence -/

namespace EpGroupoid.Examples

/-- Every map between discrete M-polyfolds is a local sc-diffeomorphism (sheets `{p} → {f p}`;
a copy of a private lemma of `Chapter7/NonVacuity.lean`). -/
theorem isLocalScDiffeo_discrete {A B : Type*} [TopologicalSpace A]
    [DiscreteTopology A] [TopologicalSpace B] [DiscreteTopology B] (f : A → B) :
    (discretePolyfold A).IsLocalScDiffeo (discretePolyfold B) f := fun p =>
  ⟨{p}, {f p}, fun _ => p, rfl,
    { isScSmoothOn := (isScSmoothMap_discrete_of_continuous continuous_of_discreteTopology).mono
        (isOpen_discrete _) (subset_univ _)
      isScSmoothOn_inv := (isScSmoothMap_const_discrete p).mono (isOpen_discrete _)
        (subset_univ _)
      mapsTo := fun q hq => by rw [mem_singleton_iff.1 hq]; exact mem_singleton _
      mapsTo_inv := fun _ _ => mem_singleton p
      left_inv := fun _ hq => (mem_singleton_iff.1 hq).symm
      right_inv := fun _ hb => (mem_singleton_iff.1 hb).symm }⟩

/-- The functor from the pair groupoid of `ℤ` (one morphism between any two objects) to the point
ep-groupoid. -/
def pairToPoint : EpFunctor pairEpGroupoid pointEpGroupoid where
  obj _ := ()
  mor _ := ()
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp _ _ _ := rfl
  mor_unit _ := rfl
  isScSmoothMap_obj := isScSmoothMap_const_discrete ()
  isScSmoothMap_mor := isScSmoothMap_const_discrete ()

/-- **A non-identity equivalence** (witness for Definition 10.1.1): `pairToPoint`. -/
theorem isEquivalence_pairToPoint : pairToPoint.IsEquivalence :=
  pairToPoint.lemma_10_1_2
    { faithful := (GroupoidFunctor.faithful_iff _).2 fun _ _ hs ht _ => Prod.ext ht hs
      full := (GroupoidFunctor.full_iff _).2 fun x x' _ _ _ => ⟨(x', x), rfl, rfl, rfl⟩
      essSurj := (GroupoidFunctor.essSurj_iff _).2 fun _ => ⟨0, (), rfl, rfl⟩ }
    (isLocalScDiffeo_discrete _)

/-- **An equivalence is in general not invertible as a functor** (2021 p. 462): `pairToPoint`
is not injective on objects, so no functor `G` has `G ∘ pairToPoint = id` on objects. -/
theorem not_exists_leftInverse_pairToPoint :
    ¬ ∃ G : EpFunctor pointEpGroupoid pairEpGroupoid, ∀ x, G.obj (pairToPoint.obj x) = x := by
  rintro ⟨G, hG⟩
  have h := (hG 0).symm.trans (hG 1)
  exact absurd h (by decide)

end EpGroupoid.Examples

end Polyfold
