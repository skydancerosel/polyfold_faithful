import Polyfold.Chapter17.Subpolyfold
import Polyfold.Chapter17.LevelOneCategory
import Polyfold.Chapter11.FaceGeneralizedIso

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.3 (pp. 785–786): the restricted uniformizers `Ψ_A`, **Lemma 17.3.5** and
**Proposition 17.3.6**.  Numbers and pages are the 2021 text's.

# The polyfold structure of a subpolyfold

## The text, paraphrased

(p. 785) For a subpolyfold `A` of `C`, an object `α` of `A` and `Ψ ∈ F(α)`, `Ψ : G ⋉ O → C`,
`Ψ_A : G ⋉ A_Ψ → A` is the restriction of `Ψ`.  "Clearly" `Ψ_A` is injective on objects and fully
faithful, and in the commutative square
`|G ⋉ A_Ψ| → |A|` over `|G ⋉ O| → |C|` the horizontal maps are homeomorphisms onto open images
and the vertical maps are topological embeddings, so every `Ψ_A` is a uniformizer.  `F_A(α)` is
the set of the `Ψ_A`, `Ψ ∈ F(α)`; the transition set `M(Ψ_A, Ψ'_A)` is a subset of `M(Ψ, Ψ')`.
(Lemma 17.3.5, p. 786) `M(Ψ_A, Ψ'_A)` is a sub-M-polyfold of `M(Ψ, Ψ')`: near `(o, φ, o')` a sheet
`s : U(o, φ, o') → U(o)` maps `U(o, φ, o') ∩ M(Ψ_A, Ψ'_A)` onto `A_Ψ ∩ U(o)`.  The structure maps
are sc-smooth as restrictions of the ambient ones.  (Proposition 17.3.6) The full subcategory `A`,
as a stand-alone GCT, inherits a natural polyfold structure `(F_A, M)`.

## What is formalized

* `GroupoidStr.fullSub_comp_coe` (composition in the full subcategory); the inclusion `A → C` is
  `GroupoidStr.fullSubInclusion` (`|A| → |C|` injective: `injective_orbitMap_fullSubInclusion`).
* `GCT.sub C A`: **the full subcategory on `A` as a GCT**, `|A|` with the topology of `|C|`
  (`GCT.isEmbedding_subOrbitMap`).
* `GroupoidStr.isEmbedding_orbitMap_translationSub`: for a `G`-invariant `B ⊆ O`,
  `|G ⋉ B| → |G ⋉ O|` is a topological embedding (the left vertical map).
* `GCT.LocalUniformizer.restrict`: **`Ψ_A : G ⋉ A_Ψ → A`**, a local uniformizer of `C.sub A`;
  `isOpenEmbedding_orbitMap_restrictFunctor` (the square of p. 786), `restrict_isAt`,
  `restrict_obj_val`, `restrict_mor_val`.
* `GCT.PolyfoldConstruction.restrictTransSet` (`s⁻¹(A_Ψ) ⊆ M(Ψ, Ψ')`),
  `mem_restrictTransSet_iff_tgt` (`= t⁻¹(A_Ψ')`), `restrictTransEquiv`
  (`M(Ψ_A, Ψ'_A) ≃ s⁻¹(A_Ψ)`); **Lemma 17.3.5**: `isSubMPolyfold_restrictTransSet`,
  `lemma_17_3_5` (sub-M-polyfold, the sheets, injective with image `s⁻¹(A_Ψ)`).
* The transition M-polyfold `RTr`, `rtrPolyfold` (the sub-M-polyfold structure, transported to
  `M(Ψ_A, Ψ'_A)` along `rtrHomeomorph`), and the structure maps: `rtr_isLocalScDiffeo_src`,
  `rtr_isLocalScDiffeo_tgt`, `rtr_isScSmoothMap_unit`, `rtr_isScSmoothMap_inv`,
  `rtr_isScSmoothMap_mul` (restrictions of the ambient ones).
* **Proposition 17.3.6**: `subF` (`F_A`), `subConstruction hS : (C.sub A).PolyfoldConstruction`
  for `hS : S.IsSubpolyfold A`, `mem_subF_iff` (`F_A(α) = {Ψ_A | Ψ ∈ F(α)}`), and
  `proposition_17_3_6` (`F_A` as stated; every transition M-polyfold of `(F_A, M)` is mapped by
  `(o, φ, o') ↦ (o, φ, o')` bijectively and as a local sc-diffeomorphism onto the
  sub-M-polyfold `s⁻¹(A_Ψ) ⊆ M(Ψ, Ψ')`, keeping morphisms and objects).
* Witness: `reflection_subConstruction` (`A = {0}` of `ℤ/2 ⋉ ℝ`: `F_A(0) ≠ ∅`, and the restricted
  uniformizer has the nontrivial group `ℤ/2`, the isotropy of `0`).

## Readings

* `|A|` carries the subspace topology of `|C|` (via the injective map `|A| → |C|`); it is
  metrizable since `|C|` is.
* The action of `G` on `A_Ψ` is the restriction (`A_Ψ` is `G`-invariant since `A` is saturated);
  `A_Ψ` carries the sub-M-polyfold structure of Proposition 2.3.19.
* "`M(Ψ_A, Ψ'_A)` is a subset of `M(Ψ, Ψ')`" is the injection `(o, φ, o') ↦ (o, φ, o')`
  (`restrictTransEquiv`); its image is `s⁻¹(A_Ψ) = t⁻¹(A_Ψ')` (saturation), and `M(Ψ_A, Ψ'_A)`
  receives the topology and the M-polyfold structure of this sub-M-polyfold.
* `F_A(α)` is the set of all `Ψ_A`, `Ψ ∈ F(α)`.  If two `Ψ₁ ≠ Ψ₂ ∈ F` have the same restriction,
  the text does not say which ambient `M(Ψ_i, Ψ')` gives `M(Ψ_A, Ψ'_A)` its structure; one of them
  is chosen (`subData`), and every statement holds for the chosen one.
* The structure maps of `(F_A, M)` are the restrictions of those of `(F, M)`; the generic
  transition data of `subConstruction` (`subTopOf`, `subMOf`, `subSrcOf`, …) are `RTr`,
  `rtrPolyfold`, `rtr_isLocalScDiffeo_src`, … at `L = Ψ_A`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

/-! ### The full subcategory on a saturated set -/

namespace GroupoidStr

variable {Obj Mor : Type u} (G : GroupoidStr Obj Mor)

/-- The composition of the full subcategory on composable morphisms. -/
theorem fullSub_comp_coe (A : Set Obj) (φ ψ : G.morOn A) (h : G.src φ.1 = G.tgt ψ.1) :
    ((G.fullSub A).comp φ ψ : Mor) = G.comp φ.1 ψ.1 := by
  simp only [GroupoidStr.fullSub, dif_pos h]

end GroupoidStr

namespace GCT

variable (C : GCT.{u})

/-- The full subcategory on `A ⊆ obj(C)` as a groupoidal category (Definition 17.1.1 (1)–(3)). -/
def fullSubGroupoidal (A : Set C.Obj) : GroupoidalCategory.{u} where
  Obj := A
  Mor := C.toGroupoidStr.morOn A
  toGroupoidStr := C.toGroupoidStr.fullSub A
  finite_mor α β := by
    refine ((C.finite_mor α.1 β.1).preimage Subtype.val_injective.injOn).subset fun φ hφ => ?_
    exact ⟨congrArg Subtype.val hφ.1, congrArg Subtype.val hφ.2⟩

/-- The map `|A| → |C|`. -/
abbrev subOrbitMap (A : Set C.Obj) :
    (C.toGroupoidStr.fullSub A).OrbitSpace → C.toGroupoidStr.OrbitSpace :=
  (C.toGroupoidStr.fullSubInclusion A).orbitMap

/-- **The full subcategory `A` on a set of objects as a stand-alone GCT** (pp. 785–786): `|A|`
with the topology of `|C|` (induced by the injective map `|A| → |C|`), metrizable. -/
def sub (A : Set C.Obj) : GCT.{u} where
  toGroupoidalCategory := C.fullSubGroupoidal A
  top := TopologicalSpace.induced (C.subOrbitMap A) inferInstance
  metrizable :=
    letI : TopologicalSpace (C.toGroupoidStr.fullSub A).OrbitSpace :=
      TopologicalSpace.induced (C.subOrbitMap A) inferInstance
    (IsEmbedding.mk ⟨rfl⟩ (C.toGroupoidStr.injective_orbitMap_fullSubInclusion A)).metrizableSpace

theorem sub_toGroupoidStr (A : Set C.Obj) :
    (C.sub A).toGroupoidStr = C.toGroupoidStr.fullSub A := rfl

/-- **`|A| → |C|` is a topological embedding.** -/
theorem isEmbedding_subOrbitMap (A : Set C.Obj) :
    @IsEmbedding _ _ (C.sub A).top _ (C.subOrbitMap A) :=
  @IsEmbedding.mk _ _ (C.sub A).top _ _ (@IsInducing.mk _ _ (C.sub A).top _ _ rfl)
    (C.toGroupoidStr.injective_orbitMap_fullSubInclusion A)

end GCT

/-! ### `|G ⋉ B| → |G ⋉ O|` for an invariant subset -/

namespace GroupoidStr

variable {G O : Type u} [Group G] [TopologicalSpace O] [MulAction G O] {B : Set O}

/-- The action of `G` on a `G`-invariant subset. -/
abbrev subMulAction (hB : ∀ (g : G) (x : O), x ∈ B → g • x ∈ B) : MulAction G B where
  smul g x := ⟨g • x.1, hB g x.1 x.2⟩
  one_smul x := Subtype.ext (one_smul G x.1)
  mul_smul g h x := Subtype.ext (mul_smul g h x.1)

/-- The inclusion `G ⋉ B → G ⋉ O` of translation groupoids. -/
def translationSubFunctor (hB : ∀ (g : G) (x : O), x ∈ B → g • x ∈ B) :
    letI := subMulAction hB
    GroupoidFunctor (GroupoidStr.translation G B) (GroupoidStr.translation G O) :=
  letI := subMulAction hB
  { obj := Subtype.val
    mor := fun p => (p.1, p.2.1)
    src_mor := fun _ => rfl
    tgt_mor := fun _ => rfl
    mor_comp := fun _ _ _ => rfl
    mor_unit := fun _ => rfl }

/-- **The left vertical map of p. 786 is a topological embedding**: for a `G`-invariant
`B ⊆ O` (`G` acting by homeomorphisms), `|G ⋉ B| → |G ⋉ O|` is a topological embedding.  For
`W` open in `|G ⋉ B|`, `π_B⁻¹(W) = B ∩ W₀` with `W₀` open in `O`, and `W` is the preimage of the
open set `π(W₀)`, since `B` is invariant. -/
theorem isEmbedding_orbitMap_translationSub (hc : ∀ g : G, Continuous fun y : O => g • y)
    (hB : ∀ (g : G) (x : O), x ∈ B → g • x ∈ B) :
    letI := subMulAction hB
    IsEmbedding (translationSubFunctor hB).orbitMap := by
  let _ := subMulAction hB
  set j := (translationSubFunctor hB).orbitMap with hj
  have hcont : Continuous j := by
    refine continuous_quot_lift _ ?_
    exact continuous_quot_mk.comp continuous_subtype_val
  have hinj : Injective j := by
    intro z w h
    induction z using Quotient.inductionOn with
    | h x =>
    induction w using Quotient.inductionOn with
    | h y =>
      obtain ⟨φ, hs, ht⟩ := ((GroupoidStr.translation G O).π_eq_π_iff).1 h
      change φ.2 = x.1 at hs
      change φ.1 • φ.2 = y.1 at ht
      refine ((GroupoidStr.translation G B).π_eq_π_iff).2 ⟨(φ.1, x), rfl, Subtype.ext ?_⟩
      change φ.1 • x.1 = y.1
      rw [← hs, ht]
  refine ⟨⟨?_⟩, hinj⟩
  apply le_antisymm
  · intro W hW
    rw [isOpen_induced_iff] at hW
    obtain ⟨W', hW', rfl⟩ := hW
    exact hW'.preimage hcont
  · intro W hW
    have hW₁ : IsOpen ((GroupoidStr.translation G B).π ⁻¹' W) := hW
    obtain ⟨W₀, hW₀, hW₀eq⟩ := isOpen_induced_iff.1 hW₁
    refine isOpen_induced_iff.2 ⟨(GroupoidStr.translation G O).π '' W₀,
      GroupoidStr.isOpenMap_π_translation hc W₀ hW₀, ?_⟩
    ext z
    induction z using Quotient.inductionOn with
    | h b =>
    simp only [mem_preimage]
    change (GroupoidStr.translation G O).π b.1 ∈ (GroupoidStr.translation G O).π '' W₀ ↔
      (GroupoidStr.translation G B).π b ∈ W
    constructor
    · rintro ⟨o, ho, hob⟩
      obtain ⟨φ, hs, ht⟩ := ((GroupoidStr.translation G O).π_eq_π_iff).1 hob
      change φ.2 = o at hs
      change φ.1 • φ.2 = b.1 at ht
      have hoB : o ∈ B := by
        have := hB φ.1⁻¹ b.1 b.2
        rwa [← ht, inv_smul_smul, hs] at this
      have hmem : (⟨o, hoB⟩ : B) ∈ (GroupoidStr.translation G B).π ⁻¹' W := by
        rw [← hW₀eq]; exact ho
      have heq : (GroupoidStr.translation G B).π ⟨o, hoB⟩ =
          (GroupoidStr.translation G B).π b :=
        ((GroupoidStr.translation G B).π_eq_π_iff).2 ⟨(φ.1, ⟨o, hoB⟩), rfl, Subtype.ext (by
          change φ.1 • o = b.1
          rw [← hs, ht])⟩
      rw [← heq]
      exact hmem
    · intro hb
      have : b ∈ (GroupoidStr.translation G B).π ⁻¹' W := hb
      rw [← hW₀eq] at this
      exact ⟨b.1, this, rfl⟩

end GroupoidStr

/-! ### The restricted uniformizer `Ψ_A` -/

namespace GCT.LocalUniformizer

variable {C : GCT.{u}} {A : Set C.Obj} (hA : C.toGroupoidStr.IsSaturated A)
  (Ψ : C.LocalUniformizer)

include hA in
/-- `A_Ψ = Ψ⁻¹(A)` is `G`-invariant (`Ψ(g, q) : Ψ(q) → Ψ(g ∗ q)` and `A` is saturated). -/
theorem smul_mem_preimage (g : Ψ.G) (q : Ψ.O) (hq : q ∈ Ψ.obj ⁻¹' A) :
    g • q ∈ Ψ.obj ⁻¹' A := by
  have h := C.toGroupoidStr.isSaturated_iff.1 hA (Ψ.toUniformizer.mor (g, q))
  rw [Ψ.toUniformizer.src_mor, Ψ.toUniformizer.tgt_mor] at h
  exact h hq

/-- The action of `G` on `A_Ψ`. -/
abbrev restrictMulAction : MulAction Ψ.G (Ψ.obj ⁻¹' A) :=
  GroupoidStr.subMulAction (Ψ.smul_mem_preimage hA)

/-- The functor `Ψ_A : G ⋉ A_Ψ → A` on the full subcategory `A`. -/
def restrictFunctor :
    letI := Ψ.restrictMulAction hA
    GroupoidFunctor (GroupoidStr.translation Ψ.G (Ψ.obj ⁻¹' A)) (C.toGroupoidStr.fullSub A) :=
  letI := Ψ.restrictMulAction hA
  { obj := fun q => ⟨Ψ.obj q.1, q.2⟩
    mor := fun p => ⟨Ψ.toUniformizer.mor (p.1, p.2.1), by
      rw [Ψ.toUniformizer.src_mor]; exact p.2.2, by
      rw [Ψ.toUniformizer.tgt_mor]; exact Ψ.smul_mem_preimage hA p.1 p.2.1 p.2.2⟩
    src_mor := fun p => Subtype.ext (Ψ.toUniformizer.src_mor (p.1, p.2.1))
    tgt_mor := fun p => Subtype.ext (Ψ.toUniformizer.tgt_mor (p.1, p.2.1))
    mor_comp := fun p p' h => by
      refine Subtype.ext ?_
      have h' : (GroupoidStr.translation Ψ.G Ψ.O).src (p.1, p.2.1) =
          (GroupoidStr.translation Ψ.G Ψ.O).tgt (p'.1, p'.2.1) := congrArg Subtype.val h
      rw [C.toGroupoidStr.fullSub_comp_coe A _ _ (by
        change C.toGroupoidStr.src (Ψ.toUniformizer.mor (p.1, p.2.1)) =
          C.toGroupoidStr.tgt (Ψ.toUniformizer.mor (p'.1, p'.2.1))
        rw [Ψ.toUniformizer.src_mor, Ψ.toUniformizer.tgt_mor]
        exact congrArg Ψ.obj h')]
      exact Ψ.functor.mor_comp (p.1, p.2.1) (p'.1, p'.2.1) h'
    mor_unit := fun q => Subtype.ext (Ψ.functor.mor_unit q.1) }

/-- **The square of p. 786**: `|Ψ_A| : |G ⋉ A_Ψ| → |A|` is a homeomorphism onto the open set
`ι⁻¹(footprint Ψ)`, where `ι : |A| → |C|` (an embedding) and `|G ⋉ A_Ψ| → |G ⋉ O|` (an embedding)
are the vertical maps. -/
theorem isOpenEmbedding_orbitMap_restrictFunctor :
    letI := Ψ.restrictMulAction hA
    @IsOpenEmbedding _ _ _ (C.sub A).top (Ψ.restrictFunctor hA).orbitMap := by
  let _ := Ψ.restrictMulAction hA
  let _ : TopologicalSpace (C.toGroupoidStr.fullSub A).OrbitSpace := (C.sub A).top
  have hc := EpGroupoid.Examples.action_continuous_smul Ψ.smooth_smul
  have hj := GroupoidStr.isEmbedding_orbitMap_translationSub hc (Ψ.smul_mem_preimage hA)
  have hsq : C.subOrbitMap A ∘ (Ψ.restrictFunctor hA).orbitMap =
      Ψ.functor.orbitMap ∘
        (GroupoidStr.translationSubFunctor (Ψ.smul_mem_preimage hA)).orbitMap := by
    funext z
    induction z using Quotient.inductionOn with
    | h _ => rfl
  have hemb : IsEmbedding (Ψ.restrictFunctor hA).orbitMap := by
    have h2 : IsEmbedding (C.subOrbitMap A ∘ (Ψ.restrictFunctor hA).orbitMap) :=
      hsq ▸ Ψ.isOpenEmbedding_orbitMap.isEmbedding.comp hj
    exact ((C.isEmbedding_subOrbitMap A).of_comp_iff).1 h2
  refine ⟨hemb, ?_⟩
  have hrange : range (Ψ.restrictFunctor hA).orbitMap = C.subOrbitMap A ⁻¹' Ψ.footprint := by
    ext z
    induction z using Quotient.inductionOn with
    | h a =>
    constructor
    · rintro ⟨w, hw⟩
      rw [mem_preimage, ← hw]
      exact ⟨_, (congrFun hsq w).symm⟩
    · intro h
      obtain ⟨q, hq⟩ := Ψ.mem_footprint_iff.1 h
      obtain ⟨φ, hs, ht⟩ := (C.toGroupoidStr.π_eq_π_iff).1 hq
      have hqA : Ψ.obj q ∈ A := by
        have h' := C.toGroupoidStr.src_mem_iff_tgt_mem_of_isSaturated hA φ
        rw [hs, ht] at h'
        exact h'.2 a.2
      refine ⟨(GroupoidStr.translation Ψ.G (Ψ.obj ⁻¹' A)).π ⟨q, hqA⟩, ?_⟩
      change (C.toGroupoidStr.fullSub A).π ⟨Ψ.obj q, hqA⟩ = (C.toGroupoidStr.fullSub A).π a
      refine ((C.toGroupoidStr.fullSub A).π_eq_π_iff).2
        ⟨⟨φ, ?_, ?_⟩, Subtype.ext hs, Subtype.ext ht⟩
      · rw [hs]; exact hqA
      · rw [ht]; exact a.2
  have ho := isOpen_induced (f := C.subOrbitMap A) Ψ.isOpen_footprint
  rw [← hrange] at ho
  exact ho

variable {Ψ} in
/-- **The restricted uniformizer `Ψ_A : G ⋉ A_Ψ → A`** (p. 785), for `A_Ψ` a sub-M-polyfold of
`O`: injective on objects, fully faithful, and `|Ψ_A|` a homeomorphism onto an open subset of
`|A|` (`restrict_isOpenEmbedding`). -/
def restrict (hΨ : Ψ.P.IsSubMPolyfold (Ψ.obj ⁻¹' A)) : (C.sub A).LocalUniformizer :=
  letI := Ψ.restrictMulAction hA
  haveI : ParacompactSpace (Ψ.obj ⁻¹' A) := Ψ.P.paracompactSpace_subtype _
  { O := Ψ.obj ⁻¹' A
    P := MPolyfold.subPolyfold hΨ
    G := Ψ.G
    smooth_smul := fun g => MPolyfold.isScSmoothOn_subPolyfold_of_val hΨ
      ((Ψ.smooth_smul g).comp (MPolyfold.subPolyfold_inclusion_isScSmooth hΨ))
    functor := Ψ.restrictFunctor hA
    injective_obj := fun q q' h => Subtype.ext (Ψ.injective_obj (congrArg Subtype.val h))
    full := (GroupoidFunctor.full_iff _).2 fun x x' ψ hs ht => by
      obtain ⟨g, hg, hψ⟩ := Ψ.toUniformizer.exists_smul_eq_mor (φ := ψ.1)
        (congrArg Subtype.val hs) (congrArg Subtype.val ht)
      exact ⟨(g, x), rfl, Subtype.ext hg, Subtype.ext hψ⟩
    faithful := (GroupoidFunctor.faithful_iff _).2 fun φ φ' hs _ he => by
      have h := Ψ.toUniformizer.mor_injective (congrArg Subtype.val he)
      have h1 : φ.1 = φ'.1 := (Prod.ext_iff.1 h).1
      exact Prod.ext h1 hs
    isOpenEmbedding_orbitMap := Ψ.isOpenEmbedding_orbitMap_restrictFunctor hA }

@[simp]
theorem restrict_obj_val (hΨ : Ψ.P.IsSubMPolyfold (Ψ.obj ⁻¹' A)) (q : Ψ.obj ⁻¹' A) :
    (show A from (Ψ.restrict hA hΨ).obj q).1 = Ψ.obj q.1 := rfl

theorem restrict_mor_val (hΨ : Ψ.P.IsSubMPolyfold (Ψ.obj ⁻¹' A)) (g : Ψ.G) (q : Ψ.obj ⁻¹' A) :
    (show C.toGroupoidStr.morOn A from (Ψ.restrict hA hΨ).toUniformizer.mor (g, q)).1 =
      Ψ.toUniformizer.mor (g, q.1) := rfl

/-- `Ψ_A` is at `α ∈ A` when `Ψ` is at `α`. -/
theorem restrict_isAt (hΨ : Ψ.P.IsSubMPolyfold (Ψ.obj ⁻¹' A)) {α : A} (h : Ψ.IsAt α.1) :
    (Ψ.restrict hA hΨ).IsAt α := by
  obtain ⟨q, hq⟩ := h
  have hqA : q ∈ Ψ.obj ⁻¹' A := by
    have hq' : Ψ.obj q = α.1 := hq
    change Ψ.obj q ∈ A
    rw [hq']; exact α.2
  exact ⟨⟨q, hqA⟩, Subtype.ext hq⟩

instance (B : Set C.Obj) : ParacompactSpace (Ψ.obj ⁻¹' B) := Ψ.P.paracompactSpace_subtype _

end GCT.LocalUniformizer

/-! ### The transition sets `M(Ψ_A, Ψ'_A)` -/

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)
  {Y : Type u} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]

/-- The inverse of the transporting homeomorphism is a local sc-diffeomorphism. -/
theorem isLocalScDiffeo_transport_symm (e : X ≃ₜ Y) :
    (P.transport e).IsLocalScDiffeo P e.symm := fun _ =>
  ⟨univ, univ, e, mem_univ _, (P.isScDiffeoOn_transport e).symm⟩

theorem isScSmoothMap_transport (e : X ≃ₜ Y) : P.IsScSmoothMap (P.transport e) e :=
  (P.isScDiffeoOn_transport e).isScSmoothOn

theorem isScSmoothMap_transport_symm (e : X ≃ₜ Y) : (P.transport e).IsScSmoothMap P e.symm :=
  (P.isScDiffeoOn_transport e).isScSmoothOn_inv

end MPolyfold

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} (S : C.PolyfoldConstruction) {A : Set C.Obj}
  (hA : C.toGroupoidStr.IsSaturated A)

/-- `s⁻¹(A_Ψ) ⊆ M(Ψ, Ψ')`: the transitions `(q, φ, q')` with `Ψ(q) ∈ A` (Lemma 17.3.5). -/
def restrictTransSet (Ψ Ψ' : S.Unif) : Set (S.Tr Ψ Ψ') := {b | Ψ.1.obj b.src ∈ A}

variable {S} in
include hA in
/-- `s⁻¹(A_Ψ) = t⁻¹(A_Ψ')` (`A` is saturated). -/
theorem mem_restrictTransSet_iff_tgt {Ψ Ψ' : S.Unif} (b : S.Tr Ψ Ψ') :
    b ∈ S.restrictTransSet (A := A) Ψ Ψ' ↔ Ψ'.1.obj b.tgt ∈ A := by
  have h := C.toGroupoidStr.src_mem_iff_tgt_mem_of_isSaturated hA b.mor
  rw [b.src_mor, b.tgt_mor] at h
  exact h

variable {S} in
/-- **Lemma 17.3.5, the sub-M-polyfold**: `s⁻¹(A_Ψ)` is a sub-M-polyfold of `M(Ψ, Ψ')`, since
`s` is a local sc-diffeomorphism and `A_Ψ` a sub-M-polyfold of `O`. -/
theorem isSubMPolyfold_restrictTransSet {Ψ : S.Unif} (Ψ' : S.Unif)
    (hp : Ψ.1.P.IsSubMPolyfold (Ψ.1.obj ⁻¹' A)) :
    (S.transPolyfold Ψ Ψ').IsSubMPolyfold (S.restrictTransSet (A := A) Ψ Ψ') :=
  (S.isLocalScDiffeo_trSrc Ψ Ψ').isSubMPolyfold_preimage hp

instance (Ψ Ψ' : S.Unif) : ParacompactSpace (S.restrictTransSet (A := A) Ψ Ψ') :=
  (S.transPolyfold Ψ Ψ').paracompactSpace_subtype _

variable (Ψ Ψ' Ψ'' : S.Unif) (p : Ψ.1.P.IsSubMPolyfold (Ψ.1.obj ⁻¹' A))
  (p' : Ψ'.1.P.IsSubMPolyfold (Ψ'.1.obj ⁻¹' A)) (p'' : Ψ''.1.P.IsSubMPolyfold (Ψ''.1.obj ⁻¹' A))

/-- **`M(Ψ_A, Ψ'_A)` as a subset of `M(Ψ, Ψ')`** (p. 786): `(o, φ, o') ↦ (o, φ, o')`, a
bijection onto `s⁻¹(A_Ψ)`. -/
def restrictTransEquiv :
    (LocalUniformizer.restrict hA p).Trans (LocalUniformizer.restrict hA p') ≃
      S.restrictTransSet (A := A) Ψ Ψ' where
  toFun a := ⟨⟨a.src.1, a.mor.1, a.tgt.1, congrArg Subtype.val a.src_mor,
    congrArg Subtype.val a.tgt_mor⟩, a.src.2⟩
  invFun b := ⟨⟨b.1.src, b.2⟩, ⟨b.1.mor, by rw [b.1.src_mor]; exact b.2, by
      rw [b.1.tgt_mor]; exact (mem_restrictTransSet_iff_tgt hA b.1).1 b.2⟩,
    ⟨b.1.tgt, (mem_restrictTransSet_iff_tgt hA b.1).1 b.2⟩, Subtype.ext b.1.src_mor,
    Subtype.ext b.1.tgt_mor⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem restrictTransEquiv_apply_src (a) :
    (S.restrictTransEquiv hA Ψ Ψ' p p' a).1.src = a.src.1 := rfl

@[simp]
theorem restrictTransEquiv_apply_mor (a) :
    (S.restrictTransEquiv hA Ψ Ψ' p p' a).1.mor = a.mor.1 := rfl

@[simp]
theorem restrictTransEquiv_apply_tgt (a) :
    (S.restrictTransEquiv hA Ψ Ψ' p p' a).1.tgt = a.tgt.1 := rfl

/-- **The transition M-polyfold `M(Ψ_A, Ψ'_A)`** (a type synonym of the transition set carrying
the topology and the M-polyfold structure of the sub-M-polyfold `s⁻¹(A_Ψ) ⊆ M(Ψ, Ψ')`). -/
def RTr : Type u := (LocalUniformizer.restrict hA p).Trans (LocalUniformizer.restrict hA p')

instance : TopologicalSpace (S.RTr hA Ψ Ψ' p p') :=
  TopologicalSpace.induced (S.restrictTransEquiv hA Ψ Ψ' p p') inferInstance

/-- `M(Ψ_A, Ψ'_A) ≃ₜ s⁻¹(A_Ψ)`. -/
def rtrHomeomorph : S.RTr hA Ψ Ψ' p p' ≃ₜ S.restrictTransSet (A := A) Ψ Ψ' :=
  Equiv.toHomeomorphOfIsInducing
    (S.restrictTransEquiv hA Ψ Ψ' p p' : S.RTr hA Ψ Ψ' p p' ≃ S.restrictTransSet (A := A) Ψ Ψ')
    ⟨rfl⟩

instance : T2Space (S.RTr hA Ψ Ψ' p p') := (S.rtrHomeomorph hA Ψ Ψ' p p').isEmbedding.t2Space

instance : ParacompactSpace (S.RTr hA Ψ Ψ' p p') :=
  (S.rtrHomeomorph hA Ψ Ψ' p p').isClosedEmbedding.paracompactSpace

/-- The M-polyfold structure of `M(Ψ_A, Ψ'_A)`: that of the sub-M-polyfold `s⁻¹(A_Ψ)` of
`M(Ψ, Ψ')`, transported along `M(Ψ_A, Ψ'_A) ≃ₜ s⁻¹(A_Ψ)`. -/
def rtrPolyfold : MPolyfold (S.RTr hA Ψ Ψ' p p') :=
  (MPolyfold.subPolyfold (isSubMPolyfold_restrictTransSet Ψ' p)).transport
    (S.rtrHomeomorph hA Ψ Ψ' p p').symm

theorem rtr_isLocalScDiffeo_homeomorph :
    (S.rtrPolyfold hA Ψ Ψ' p p').IsLocalScDiffeo
      (MPolyfold.subPolyfold (isSubMPolyfold_restrictTransSet Ψ' p))
      (S.rtrHomeomorph hA Ψ Ψ' p p') :=
  MPolyfold.isLocalScDiffeo_transport_symm _ (S.rtrHomeomorph hA Ψ Ψ' p p').symm

theorem rtr_isScSmoothMap_homeomorph_symm :
    (MPolyfold.subPolyfold (isSubMPolyfold_restrictTransSet Ψ' p)).IsScSmoothMap
      (S.rtrPolyfold hA Ψ Ψ' p p') (S.rtrHomeomorph hA Ψ Ψ' p p').symm :=
  MPolyfold.isScSmoothMap_transport _ (S.rtrHomeomorph hA Ψ Ψ' p p').symm

/-- **Definition 17.1.8 (a) for `Ψ_A`**: `s : M(Ψ_A, Ψ'_A) → A_Ψ` is a local sc-diffeomorphism. -/
theorem rtr_isLocalScDiffeo_src :
    (S.rtrPolyfold hA Ψ Ψ' p p').IsLocalScDiffeo (LocalUniformizer.restrict hA p).P
      fun a : S.RTr hA Ψ Ψ' p p' => a.src := by
  have h1 := MPolyfold.isLocalScDiffeo_subPolyfold_of_iff (S.isLocalScDiffeo_trSrc Ψ Ψ') p
    (isSubMPolyfold_restrictTransSet Ψ' p) (fun _ => Iff.rfl)
    (f' := fun b : S.restrictTransSet (A := A) Ψ Ψ' => (⟨b.1.src, b.2⟩ : Ψ.1.obj ⁻¹' A))
    fun _ => rfl
  exact h1.comp (S.rtr_isLocalScDiffeo_homeomorph hA Ψ Ψ' p p')

/-- **Definition 17.1.8 (a) for `Ψ_A`**: `t : M(Ψ_A, Ψ'_A) → A_Ψ'` is a local sc-diffeomorphism. -/
theorem rtr_isLocalScDiffeo_tgt :
    (S.rtrPolyfold hA Ψ Ψ' p p').IsLocalScDiffeo (LocalUniformizer.restrict hA p').P
      fun a : S.RTr hA Ψ Ψ' p p' => a.tgt := by
  have h1 := MPolyfold.isLocalScDiffeo_subPolyfold_of_iff (S.isLocalScDiffeo_trTgt Ψ Ψ') p'
    (isSubMPolyfold_restrictTransSet Ψ' p) (mem_restrictTransSet_iff_tgt hA)
    (f' := fun b : S.restrictTransSet (A := A) Ψ Ψ' =>
      (⟨b.1.tgt, (mem_restrictTransSet_iff_tgt hA b.1).1 b.2⟩ : Ψ'.1.obj ⁻¹' A))
    fun _ => rfl
  exact h1.comp (S.rtr_isLocalScDiffeo_homeomorph hA Ψ Ψ' p p')

/-- An element of `M(Ψ_A, Ψ'_A)` as an element of the transition M-polyfold. -/
abbrev toRTr {Ψ Ψ' : S.Unif} {p : Ψ.1.P.IsSubMPolyfold (Ψ.1.obj ⁻¹' A)}
    {p' : Ψ'.1.P.IsSubMPolyfold (Ψ'.1.obj ⁻¹' A)}
    (a : (LocalUniformizer.restrict hA p).Trans (LocalUniformizer.restrict hA p')) :
    S.RTr hA Ψ Ψ' p p' := a

/-- **Definition 17.1.8 (b) for `Ψ_A`**: the unit map `A_Ψ → M(Ψ_A, Ψ_A)` is sc-smooth. -/
theorem rtr_isScSmoothMap_unit :
    (LocalUniformizer.restrict hA p).P.IsScSmoothMap (S.rtrPolyfold hA Ψ Ψ p p)
      fun q => S.toRTr hA (GroupoidStr.TransitionSet.unit q) := by
  have hB := isSubMPolyfold_restrictTransSet (S := S) Ψ p
  have hu : (MPolyfold.subPolyfold p).IsScSmoothMap (MPolyfold.subPolyfold hB)
      fun q : Ψ.1.obj ⁻¹' A =>
        (⟨S.toTr (GroupoidStr.TransitionSet.unit q.1), q.2⟩ : S.restrictTransSet (A := A) Ψ Ψ) :=
    MPolyfold.isScSmoothOn_subPolyfold_of_val hB
      ((S.isScSmoothMap_trUnit Ψ).comp (MPolyfold.subPolyfold_inclusion_isScSmooth p))
  exact (S.rtr_isScSmoothMap_homeomorph_symm hA Ψ Ψ p p).comp hu

/-- **Definition 17.1.8 (b) for `Ψ_A`**: the inversion `M(Ψ_A, Ψ'_A) → M(Ψ'_A, Ψ_A)` is
sc-smooth. -/
theorem rtr_isScSmoothMap_inv :
    (S.rtrPolyfold hA Ψ Ψ' p p').IsScSmoothMap (S.rtrPolyfold hA Ψ' Ψ p' p)
      fun a : S.RTr hA Ψ Ψ' p p' => S.toRTr hA (GroupoidStr.TransitionSet.inv a) := by
  have hB := isSubMPolyfold_restrictTransSet (S := S) Ψ' p
  have hB' := isSubMPolyfold_restrictTransSet (S := S) Ψ p'
  have hi : (MPolyfold.subPolyfold hB).IsScSmoothMap (MPolyfold.subPolyfold hB')
      fun b : S.restrictTransSet (A := A) Ψ Ψ' =>
        (⟨S.toTr (GroupoidStr.TransitionSet.inv b.1), (mem_restrictTransSet_iff_tgt hA b.1).1 b.2⟩ :
          S.restrictTransSet (A := A) Ψ' Ψ) :=
    MPolyfold.isScSmoothOn_subPolyfold_of_val hB'
      ((S.isScSmoothMap_trInv Ψ Ψ').comp (MPolyfold.subPolyfold_inclusion_isScSmooth hB))
  exact (S.rtr_isScSmoothMap_homeomorph_symm hA Ψ' Ψ p' p).comp
    (hi.comp (S.rtr_isLocalScDiffeo_homeomorph hA Ψ Ψ' p p').isScSmoothMap)

/-- **Definition 17.1.8 (c) for `Ψ_A`**: the multiplication
`M(Ψ'_A, Ψ''_A) ₛ×ₜ M(Ψ_A, Ψ'_A) → M(Ψ_A, Ψ''_A)` is sc-smooth: it is the multiplication of
`M(Ψ', Ψ'') ₛ×ₜ M(Ψ, Ψ')` composed with the inclusion of the fibred products. -/
theorem rtr_isScSmoothMap_mul :
    MPolyfold.IsScSmoothOnFibredProduct (S.rtrPolyfold hA Ψ' Ψ'' p' p'')
      (S.rtrPolyfold hA Ψ Ψ' p p') (S.rtrPolyfold hA Ψ Ψ'' p p'')
      (S.rtr_isLocalScDiffeo_src hA Ψ' Ψ'' p' p'')
      (S.rtr_isLocalScDiffeo_tgt hA Ψ Ψ' p p').isScSmoothMap
      fun x => S.toRTr hA (GroupoidStr.TransitionSet.mul x) := by
  let P₁ := S.rtrPolyfold hA Ψ' Ψ'' p' p''
  let P₂ := S.rtrPolyfold hA Ψ Ψ' p p'
  let _ := MPolyfold.paracompactSpace_prod P₁ P₂
  let _ := (P₁.prod P₂).paracompactSpace_subtype
    (MPolyfold.fibredProduct (fun a : S.RTr hA Ψ' Ψ'' p' p'' => a.src)
      (fun a : S.RTr hA Ψ Ψ' p p' => a.tgt))
  let _ := MPolyfold.paracompactSpace_prod (S.transPolyfold Ψ' Ψ'') (S.transPolyfold Ψ Ψ')
  let _ := ((S.transPolyfold Ψ' Ψ'').prod (S.transPolyfold Ψ Ψ')).paracompactSpace_subtype
    (MPolyfold.fibredProduct (fun a : S.Tr Ψ' Ψ'' => a.src) (fun a : S.Tr Ψ Ψ' => a.tgt))
  have hF := MPolyfold.isSubMPolyfold_fibredProduct (S.isLocalScDiffeo_trSrc Ψ' Ψ'')
    (S.isLocalScDiffeo_trTgt Ψ Ψ').isScSmoothMap
  have hF' := MPolyfold.isSubMPolyfold_fibredProduct (S.rtr_isLocalScDiffeo_src hA Ψ' Ψ'' p' p'')
    (S.rtr_isLocalScDiffeo_tgt hA Ψ Ψ' p p').isScSmoothMap
  have hm : (MPolyfold.subPolyfold hF).IsScSmoothMap (S.transPolyfold Ψ Ψ'')
      fun x => S.toTr (GroupoidStr.TransitionSet.mul x) := S.isScSmoothMap_trMul Ψ Ψ' Ψ''
  have hB₃ := isSubMPolyfold_restrictTransSet (S := S) Ψ'' p
  let e₁ := S.rtrHomeomorph hA Ψ' Ψ'' p' p''
  let e₂ := S.rtrHomeomorph hA Ψ Ψ' p p'
  let j : MPolyfold.fibredProduct (fun a : S.RTr hA Ψ' Ψ'' p' p'' => a.src)
      (fun a : S.RTr hA Ψ Ψ' p p' => a.tgt) →
      MPolyfold.fibredProduct (fun a : S.Tr Ψ' Ψ'' => a.src) (fun a : S.Tr Ψ Ψ' => a.tgt) :=
    fun x => ⟨((e₁ x.1.1).1, (e₂ x.1.2).1), congrArg Subtype.val x.2⟩
  have hi := MPolyfold.subPolyfold_inclusion_isScSmooth hF'
  have h1 : (MPolyfold.subPolyfold hF').IsScSmoothMap (S.transPolyfold Ψ' Ψ'')
      fun x => (e₁ x.1.1).1 :=
    (MPolyfold.subPolyfold_inclusion_isScSmooth (isSubMPolyfold_restrictTransSet Ψ'' p')).comp
      ((S.rtr_isLocalScDiffeo_homeomorph hA Ψ' Ψ'' p' p'').isScSmoothMap.comp
        ((MPolyfold.isScSmoothMap_fst P₁ P₂).comp hi))
  have h2 : (MPolyfold.subPolyfold hF').IsScSmoothMap (S.transPolyfold Ψ Ψ')
      fun x => (e₂ x.1.2).1 :=
    (MPolyfold.subPolyfold_inclusion_isScSmooth (isSubMPolyfold_restrictTransSet Ψ' p)).comp
      ((S.rtr_isLocalScDiffeo_homeomorph hA Ψ Ψ' p p').isScSmoothMap.comp
        ((MPolyfold.isScSmoothMap_snd P₁ P₂).comp hi))
  have hj : (MPolyfold.subPolyfold hF').IsScSmoothMap (MPolyfold.subPolyfold hF) j :=
    MPolyfold.isScSmoothOn_subPolyfold_of_val hF (MPolyfold.IsScSmoothOn.prodMk h1 h2)
  let mB : MPolyfold.fibredProduct (fun a : S.RTr hA Ψ' Ψ'' p' p'' => a.src)
      (fun a : S.RTr hA Ψ Ψ' p p' => a.tgt) → S.restrictTransSet (A := A) Ψ Ψ'' :=
    fun x => ⟨S.toTr (GroupoidStr.TransitionSet.mul (j x)), x.1.2.src.2⟩
  have hmB : (MPolyfold.subPolyfold hF').IsScSmoothMap (MPolyfold.subPolyfold hB₃) mB :=
    MPolyfold.isScSmoothOn_subPolyfold_of_val hB₃ (hm.comp hj)
  change (MPolyfold.subPolyfold hF').IsScSmoothMap (S.rtrPolyfold hA Ψ Ψ'' p p'') _
  refine ((S.rtr_isScSmoothMap_homeomorph_symm hA Ψ Ψ'' p p'').comp hmB).congr fun x _ => ?_
  refine GroupoidStr.TransitionSet.ext rfl (Subtype.ext ?_) rfl
  exact (C.toGroupoidStr.fullSub_comp_coe A _ _
    (congrArg Subtype.val (GroupoidStr.TransitionSet.mor_composable_of_src_eq_tgt x.2))).symm

/-- **Lemma 17.3.5** (p. 786): for `Ψ, Ψ'` with `A_Ψ, A_Ψ'` sub-M-polyfolds, `s⁻¹(A_Ψ)` is a
sub-M-polyfold of `M(Ψ, Ψ')`; it equals `t⁻¹(A_Ψ')`; near every point a sheet
`s : U → V ⊆ O` maps `U ∩ s⁻¹(A_Ψ)` onto `V ∩ A_Ψ`; and `M(Ψ_A, Ψ'_A) → M(Ψ, Ψ')`,
`(o, φ, o') ↦ (o, φ, o')`, is injective with image `s⁻¹(A_Ψ)`. -/
theorem lemma_17_3_5 :
    (S.transPolyfold Ψ Ψ').IsSubMPolyfold (S.restrictTransSet (A := A) Ψ Ψ') ∧
      (∀ b : S.Tr Ψ Ψ', b ∈ S.restrictTransSet (A := A) Ψ Ψ' ↔ Ψ'.1.obj b.tgt ∈ A) ∧
      (∀ b : S.Tr Ψ Ψ', ∃ U V g, b ∈ U ∧
        (S.transPolyfold Ψ Ψ').IsScDiffeoOn Ψ.1.P (fun a : S.Tr Ψ Ψ' => a.src) g U V ∧
        (fun a : S.Tr Ψ Ψ' => a.src) '' (U ∩ S.restrictTransSet (A := A) Ψ Ψ') =
          V ∩ Ψ.1.obj ⁻¹' A) ∧
      Injective (fun a => (S.restrictTransEquiv hA Ψ Ψ' p p' a).1) ∧
      range (fun a => (S.restrictTransEquiv hA Ψ Ψ' p p' a).1) =
        S.restrictTransSet (A := A) Ψ Ψ' := by
  refine ⟨isSubMPolyfold_restrictTransSet Ψ' p, mem_restrictTransSet_iff_tgt hA, fun b => ?_,
    Subtype.val_injective.comp (S.restrictTransEquiv hA Ψ Ψ' p p').injective, ?_⟩
  · obtain ⟨U, V, g, hb, hd⟩ := S.isLocalScDiffeo_trSrc Ψ Ψ' b
    refine ⟨U, V, g, hb, hd, ?_⟩
    ext y
    constructor
    · rintro ⟨x, ⟨hxU, hxB⟩, rfl⟩
      exact ⟨hd.mapsTo hxU, hxB⟩
    · rintro ⟨hyV, hyA⟩
      refine ⟨g y, ⟨hd.mapsTo_inv hyV, ?_⟩, hd.right_inv y hyV⟩
      have h : (g y).src = y := hd.right_inv y hyV
      change (g y).src ∈ Ψ.1.obj ⁻¹' A
      exact h.symm ▸ hyA
  · ext b
    constructor
    · rintro ⟨a, rfl⟩
      exact (S.restrictTransEquiv hA Ψ Ψ' p p' a).2
    · intro hb
      exact ⟨(S.restrictTransEquiv hA Ψ Ψ' p p').symm ⟨b, hb⟩,
        congrArg Subtype.val ((S.restrictTransEquiv hA Ψ Ψ' p p').apply_symm_apply ⟨b, hb⟩)⟩

/-! ### The polyfold structure `(F_A, M)` -/

/-- **`F_A(α)`** (p. 786): the restrictions `Ψ_A` of the `Ψ ∈ F(α)` with `A_Ψ` a sub-M-polyfold
(all of them, for a subpolyfold `A`: `mem_subF_iff`). -/
def subF (α : (C.sub A).Obj) : Set (C.sub A).LocalUniformizer :=
  {L | ∃ Ψ ∈ S.F (show A from α).1, ∃ p : Ψ.P.IsSubMPolyfold (Ψ.obj ⁻¹' A),
    L = LocalUniformizer.restrict hA p}

theorem exists_subData (L : GCT.Unif (S.subF hA)) :
    ∃ Ψ : S.Unif, ∃ p : Ψ.1.P.IsSubMPolyfold (Ψ.1.obj ⁻¹' A),
      L.1 = LocalUniformizer.restrict hA p := by
  obtain ⟨L, α, Ψ, hΨ, p, rfl⟩ := L
  exact ⟨⟨Ψ, _, hΨ⟩, p, rfl⟩

/-- The uniformizer `Ψ ∈ F` chosen for `L ∈ F_A` with `L = Ψ_A`. -/
def subData (L : GCT.Unif (S.subF hA)) : S.Unif := (S.exists_subData hA L).choose

theorem subData_sub (L : GCT.Unif (S.subF hA)) :
    (S.subData hA L).1.P.IsSubMPolyfold ((S.subData hA L).1.obj ⁻¹' A) :=
  (S.exists_subData hA L).choose_spec.choose

theorem subData_eq (L : GCT.Unif (S.subF hA)) :
    L.1 = LocalUniformizer.restrict hA (S.subData_sub hA L) :=
  (S.exists_subData hA L).choose_spec.choose_spec

/-- The topology of `M(L, L')` for `L = Ψ_A`, `L' = Ψ'_A`. -/
@[instance_reducible]
def subTopOf : ∀ (L L' : (C.sub A).LocalUniformizer) (Ψ Ψ' : S.Unif)
    (p : Ψ.1.P.IsSubMPolyfold (Ψ.1.obj ⁻¹' A)) (p' : Ψ'.1.P.IsSubMPolyfold (Ψ'.1.obj ⁻¹' A)),
    L = LocalUniformizer.restrict hA p → L' = LocalUniformizer.restrict hA p' →
    TopologicalSpace (L.Trans L')
  | _, _, Ψ, Ψ', p, p', rfl, rfl => (inferInstance : TopologicalSpace (S.RTr hA Ψ Ψ' p p'))

theorem subT2Of : ∀ (L L' : (C.sub A).LocalUniformizer) (Ψ Ψ' : S.Unif)
    (p : Ψ.1.P.IsSubMPolyfold (Ψ.1.obj ⁻¹' A)) (p' : Ψ'.1.P.IsSubMPolyfold (Ψ'.1.obj ⁻¹' A))
    (h : L = LocalUniformizer.restrict hA p) (h' : L' = LocalUniformizer.restrict hA p'),
    @T2Space (L.Trans L') (S.subTopOf hA L L' Ψ Ψ' p p' h h')
  | _, _, Ψ, Ψ', p, p', rfl, rfl => (inferInstance : T2Space (S.RTr hA Ψ Ψ' p p'))

theorem subParaOf : ∀ (L L' : (C.sub A).LocalUniformizer) (Ψ Ψ' : S.Unif)
    (p : Ψ.1.P.IsSubMPolyfold (Ψ.1.obj ⁻¹' A)) (p' : Ψ'.1.P.IsSubMPolyfold (Ψ'.1.obj ⁻¹' A))
    (h : L = LocalUniformizer.restrict hA p) (h' : L' = LocalUniformizer.restrict hA p'),
    @ParacompactSpace (L.Trans L') (S.subTopOf hA L L' Ψ Ψ' p p' h h')
  | _, _, Ψ, Ψ', p, p', rfl, rfl => (inferInstance : ParacompactSpace (S.RTr hA Ψ Ψ' p p'))

/-- The M-polyfold `M(L, L')` for `L = Ψ_A`, `L' = Ψ'_A`: `rtrPolyfold`. -/
def subMOf : ∀ (L L' : (C.sub A).LocalUniformizer) (Ψ Ψ' : S.Unif)
    (p : Ψ.1.P.IsSubMPolyfold (Ψ.1.obj ⁻¹' A)) (p' : Ψ'.1.P.IsSubMPolyfold (Ψ'.1.obj ⁻¹' A))
    (h : L = LocalUniformizer.restrict hA p) (h' : L' = LocalUniformizer.restrict hA p'),
    @MPolyfold (L.Trans L') (S.subTopOf hA L L' Ψ Ψ' p p' h h') (S.subT2Of hA L L' Ψ Ψ' p p' h h')
      (S.subParaOf hA L L' Ψ Ψ' p p' h h')
  | _, _, Ψ, Ψ', p, p', rfl, rfl => S.rtrPolyfold hA Ψ Ψ' p p'

/-- The map `M(L, L') → s⁻¹(A_Ψ) ⊆ M(Ψ, Ψ')` for `L = Ψ_A`, `L' = Ψ'_A`. -/
def subInclOf : ∀ (L L' : (C.sub A).LocalUniformizer) (Ψ Ψ' : S.Unif)
    (p : Ψ.1.P.IsSubMPolyfold (Ψ.1.obj ⁻¹' A)) (p' : Ψ'.1.P.IsSubMPolyfold (Ψ'.1.obj ⁻¹' A)),
    L = LocalUniformizer.restrict hA p → L' = LocalUniformizer.restrict hA p' →
    L.Trans L' → S.restrictTransSet (A := A) Ψ Ψ'
  | _, _, Ψ, Ψ', p, p', rfl, rfl => S.restrictTransEquiv hA Ψ Ψ' p p'

theorem subSrcOf : ∀ (L L' : (C.sub A).LocalUniformizer) (Ψ Ψ' : S.Unif)
    (p : Ψ.1.P.IsSubMPolyfold (Ψ.1.obj ⁻¹' A)) (p' : Ψ'.1.P.IsSubMPolyfold (Ψ'.1.obj ⁻¹' A))
    (h : L = LocalUniformizer.restrict hA p) (h' : L' = LocalUniformizer.restrict hA p'),
    letI := S.subTopOf hA L L' Ψ Ψ' p p' h h'
    letI := S.subT2Of hA L L' Ψ Ψ' p p' h h'
    letI := S.subParaOf hA L L' Ψ Ψ' p p' h h'
    (S.subMOf hA L L' Ψ Ψ' p p' h h').IsLocalScDiffeo L.P GroupoidStr.TransitionSet.src
  | _, _, Ψ, Ψ', p, p', rfl, rfl => S.rtr_isLocalScDiffeo_src hA Ψ Ψ' p p'

theorem subTgtOf : ∀ (L L' : (C.sub A).LocalUniformizer) (Ψ Ψ' : S.Unif)
    (p : Ψ.1.P.IsSubMPolyfold (Ψ.1.obj ⁻¹' A)) (p' : Ψ'.1.P.IsSubMPolyfold (Ψ'.1.obj ⁻¹' A))
    (h : L = LocalUniformizer.restrict hA p) (h' : L' = LocalUniformizer.restrict hA p'),
    letI := S.subTopOf hA L L' Ψ Ψ' p p' h h'
    letI := S.subT2Of hA L L' Ψ Ψ' p p' h h'
    letI := S.subParaOf hA L L' Ψ Ψ' p p' h h'
    (S.subMOf hA L L' Ψ Ψ' p p' h h').IsLocalScDiffeo L'.P GroupoidStr.TransitionSet.tgt
  | _, _, Ψ, Ψ', p, p', rfl, rfl => S.rtr_isLocalScDiffeo_tgt hA Ψ Ψ' p p'

theorem subUnitOf : ∀ (L : (C.sub A).LocalUniformizer) (Ψ : S.Unif)
    (p : Ψ.1.P.IsSubMPolyfold (Ψ.1.obj ⁻¹' A)) (h : L = LocalUniformizer.restrict hA p),
    letI := S.subTopOf hA L L Ψ Ψ p p h h
    letI := S.subT2Of hA L L Ψ Ψ p p h h
    letI := S.subParaOf hA L L Ψ Ψ p p h h
    L.P.IsScSmoothMap (S.subMOf hA L L Ψ Ψ p p h h) GroupoidStr.TransitionSet.unit
  | _, Ψ, p, rfl => S.rtr_isScSmoothMap_unit hA Ψ p

theorem subInvOf : ∀ (L L' : (C.sub A).LocalUniformizer) (Ψ Ψ' : S.Unif)
    (p : Ψ.1.P.IsSubMPolyfold (Ψ.1.obj ⁻¹' A)) (p' : Ψ'.1.P.IsSubMPolyfold (Ψ'.1.obj ⁻¹' A))
    (h : L = LocalUniformizer.restrict hA p) (h' : L' = LocalUniformizer.restrict hA p'),
    letI := S.subTopOf hA L L' Ψ Ψ' p p' h h'
    letI := S.subT2Of hA L L' Ψ Ψ' p p' h h'
    letI := S.subParaOf hA L L' Ψ Ψ' p p' h h'
    letI := S.subTopOf hA L' L Ψ' Ψ p' p h' h
    letI := S.subT2Of hA L' L Ψ' Ψ p' p h' h
    letI := S.subParaOf hA L' L Ψ' Ψ p' p h' h
    (S.subMOf hA L L' Ψ Ψ' p p' h h').IsScSmoothMap (S.subMOf hA L' L Ψ' Ψ p' p h' h)
      GroupoidStr.TransitionSet.inv
  | _, _, Ψ, Ψ', p, p', rfl, rfl => S.rtr_isScSmoothMap_inv hA Ψ Ψ' p p'

theorem subMulOf : ∀ (L L' L'' : (C.sub A).LocalUniformizer) (Ψ Ψ' Ψ'' : S.Unif)
    (p : Ψ.1.P.IsSubMPolyfold (Ψ.1.obj ⁻¹' A)) (p' : Ψ'.1.P.IsSubMPolyfold (Ψ'.1.obj ⁻¹' A))
    (p'' : Ψ''.1.P.IsSubMPolyfold (Ψ''.1.obj ⁻¹' A))
    (h : L = LocalUniformizer.restrict hA p) (h' : L' = LocalUniformizer.restrict hA p')
    (h'' : L'' = LocalUniformizer.restrict hA p''),
    letI := S.subTopOf hA L' L'' Ψ' Ψ'' p' p'' h' h''
    letI := S.subT2Of hA L' L'' Ψ' Ψ'' p' p'' h' h''
    letI := S.subParaOf hA L' L'' Ψ' Ψ'' p' p'' h' h''
    letI := S.subTopOf hA L L' Ψ Ψ' p p' h h'
    letI := S.subT2Of hA L L' Ψ Ψ' p p' h h'
    letI := S.subParaOf hA L L' Ψ Ψ' p p' h h'
    letI := S.subTopOf hA L L'' Ψ Ψ'' p p'' h h''
    letI := S.subT2Of hA L L'' Ψ Ψ'' p p'' h h''
    letI := S.subParaOf hA L L'' Ψ Ψ'' p p'' h h''
    MPolyfold.IsScSmoothOnFibredProduct (S.subMOf hA L' L'' Ψ' Ψ'' p' p'' h' h'')
      (S.subMOf hA L L' Ψ Ψ' p p' h h') (S.subMOf hA L L'' Ψ Ψ'' p p'' h h'')
      (S.subSrcOf hA L' L'' Ψ' Ψ'' p' p'' h' h'')
      (S.subTgtOf hA L L' Ψ Ψ' p p' h h').isScSmoothMap GroupoidStr.TransitionSet.mul
  | _, _, _, Ψ, Ψ', Ψ'', p, p', p'', rfl, rfl, rfl => S.rtr_isScSmoothMap_mul hA Ψ Ψ' Ψ'' p p' p''

theorem subInclOf_spec : ∀ (L L' : (C.sub A).LocalUniformizer) (Ψ Ψ' : S.Unif)
    (p : Ψ.1.P.IsSubMPolyfold (Ψ.1.obj ⁻¹' A)) (p' : Ψ'.1.P.IsSubMPolyfold (Ψ'.1.obj ⁻¹' A))
    (h : L = LocalUniformizer.restrict hA p) (h' : L' = LocalUniformizer.restrict hA p'),
    letI := S.subTopOf hA L L' Ψ Ψ' p p' h h'
    letI := S.subT2Of hA L L' Ψ Ψ' p p' h h'
    letI := S.subParaOf hA L L' Ψ Ψ' p p' h h'
    Bijective (S.subInclOf hA L L' Ψ Ψ' p p' h h') ∧
      (S.subMOf hA L L' Ψ Ψ' p p' h h').IsLocalScDiffeo
        (MPolyfold.subPolyfold (isSubMPolyfold_restrictTransSet Ψ' p))
        (S.subInclOf hA L L' Ψ Ψ' p p' h h') ∧
      ∀ a : L.Trans L', (S.subInclOf hA L L' Ψ Ψ' p p' h h' a).1.mor =
          (show C.toGroupoidStr.morOn A from a.mor).1 ∧
        Ψ.1.obj (S.subInclOf hA L L' Ψ Ψ' p p' h h' a).1.src = (show A from L.obj a.src).1 ∧
        Ψ'.1.obj (S.subInclOf hA L L' Ψ Ψ' p p' h h' a).1.tgt = (show A from L'.obj a.tgt).1
  | _, _, Ψ, Ψ', p, p', rfl, rfl =>
    ⟨(S.restrictTransEquiv hA Ψ Ψ' p p').bijective, S.rtr_isLocalScDiffeo_homeomorph hA Ψ Ψ' p p',
      fun _ => ⟨rfl, rfl, rfl⟩⟩

variable {S} in
/-- **Proposition 17.3.6** (p. 786), the construction: for a subpolyfold `A` of `C`, the full
subcategory `A` (a GCT, `C.sub A`) carries the polyfold structure `(F_A, M)`: `F_A(α)` consists
of the restrictions `Ψ_A`, `Ψ ∈ F(α)`, and `M(Ψ_A, Ψ'_A)` is the sub-M-polyfold `s⁻¹(A_Ψ)` of
`M(Ψ, Ψ')` (Lemma 17.3.5). -/
def subConstruction (hS : S.IsSubpolyfold A) : (C.sub A).PolyfoldConstruction where
  F := S.subF hS.1
  isAt α L hL := by
    obtain ⟨Ψ, hΨ, p, rfl⟩ := hL
    exact LocalUniformizer.restrict_isAt hS.1 Ψ p (S.isAt _ Ψ hΨ)
  topM L L' := S.subTopOf hS.1 L.1 L'.1 (S.subData hS.1 L) (S.subData hS.1 L')
    (S.subData_sub hS.1 L) (S.subData_sub hS.1 L') (S.subData_eq hS.1 L) (S.subData_eq hS.1 L')
  t2M L L' := S.subT2Of hS.1 L.1 L'.1 (S.subData hS.1 L) (S.subData hS.1 L')
    (S.subData_sub hS.1 L) (S.subData_sub hS.1 L') (S.subData_eq hS.1 L) (S.subData_eq hS.1 L')
  paraM L L' := S.subParaOf hS.1 L.1 L'.1 (S.subData hS.1 L) (S.subData hS.1 L')
    (S.subData_sub hS.1 L) (S.subData_sub hS.1 L') (S.subData_eq hS.1 L) (S.subData_eq hS.1 L')
  M L L' := S.subMOf hS.1 L.1 L'.1 (S.subData hS.1 L) (S.subData hS.1 L')
    (S.subData_sub hS.1 L) (S.subData_sub hS.1 L') (S.subData_eq hS.1 L) (S.subData_eq hS.1 L')
  isLocalScDiffeo_src L L' := S.subSrcOf hS.1 L.1 L'.1 (S.subData hS.1 L) (S.subData hS.1 L')
    (S.subData_sub hS.1 L) (S.subData_sub hS.1 L') (S.subData_eq hS.1 L) (S.subData_eq hS.1 L')
  isLocalScDiffeo_tgt L L' := S.subTgtOf hS.1 L.1 L'.1 (S.subData hS.1 L) (S.subData hS.1 L')
    (S.subData_sub hS.1 L) (S.subData_sub hS.1 L') (S.subData_eq hS.1 L) (S.subData_eq hS.1 L')
  isScSmoothMap_unit L := S.subUnitOf hS.1 L.1 (S.subData hS.1 L) (S.subData_sub hS.1 L)
    (S.subData_eq hS.1 L)
  isScSmoothMap_inv L L' := S.subInvOf hS.1 L.1 L'.1 (S.subData hS.1 L) (S.subData hS.1 L')
    (S.subData_sub hS.1 L) (S.subData_sub hS.1 L') (S.subData_eq hS.1 L) (S.subData_eq hS.1 L')
  isScSmoothMap_mul L L' L'' := S.subMulOf hS.1 L.1 L'.1 L''.1 (S.subData hS.1 L)
    (S.subData hS.1 L') (S.subData hS.1 L'') (S.subData_sub hS.1 L) (S.subData_sub hS.1 L')
    (S.subData_sub hS.1 L'') (S.subData_eq hS.1 L) (S.subData_eq hS.1 L')
    (S.subData_eq hS.1 L'')

variable {S}

/-- **`F_A(α) = {Ψ_A | Ψ ∈ F(α)}`** for a subpolyfold `A` (p. 786). -/
theorem mem_subF_iff (hS : S.IsSubpolyfold A) (α : (C.sub A).Obj)
    (L : (C.sub A).LocalUniformizer) :
    L ∈ (subConstruction hS).F α ↔ ∃ Ψ, ∃ hΨ : Ψ ∈ S.F (show A from α).1,
      L = LocalUniformizer.restrict hS.1 (hS.2 _ (show A from α).2 Ψ hΨ) :=
  ⟨fun ⟨Ψ, hΨ, _, h⟩ => ⟨Ψ, hΨ, h⟩, fun ⟨Ψ, hΨ, h⟩ => ⟨Ψ, hΨ, _, h⟩⟩

/-- **Proposition 17.3.6** (p. 786): for a subpolyfold `A` of `C`, `(F_A, M)` is a polyfold
structure on the full subcategory `A` (`subConstruction hS`), where
* `F_A(α)` is the set of restrictions `Ψ_A`, `Ψ ∈ F(α)`;
* every `L ∈ F_A` is `Ψ_A` for the chosen `Ψ = subData L`, and the transition M-polyfold
  `M(L, L')` is the sub-M-polyfold `s⁻¹(A_Ψ) ⊆ M(Ψ, Ψ')` (Lemma 17.3.5): the map
  `(o, φ, o') ↦ (o, φ, o')` is a bijection onto `s⁻¹(A_Ψ)` and a local sc-diffeomorphism for its
  sub-M-polyfold structure, hence sc-smooth into `M(Ψ, Ψ')`, and it keeps the morphism and the
  objects. -/
theorem proposition_17_3_6 (hS : S.IsSubpolyfold A) :
    (∀ α L, L ∈ (subConstruction hS).F α ↔ ∃ Ψ, ∃ hΨ : Ψ ∈ S.F (show A from α).1,
      L = LocalUniformizer.restrict hS.1 (hS.2 _ (show A from α).2 Ψ hΨ)) ∧
    ∀ L L' : (subConstruction hS).Unif,
      L.1 = LocalUniformizer.restrict hS.1 (S.subData_sub hS.1 L) ∧
      ∃ ι : (subConstruction hS).Tr L L' →
          S.restrictTransSet (A := A) (S.subData hS.1 L) (S.subData hS.1 L'),
        Bijective ι ∧
        ((subConstruction hS).transPolyfold L L').IsLocalScDiffeo
          (MPolyfold.subPolyfold
            (isSubMPolyfold_restrictTransSet (S.subData hS.1 L') (S.subData_sub hS.1 L))) ι ∧
        ((subConstruction hS).transPolyfold L L').IsScSmoothMap
          (S.transPolyfold (S.subData hS.1 L) (S.subData hS.1 L')) (fun a => (ι a).1) ∧
        ∀ a : (subConstruction hS).Tr L L',
          (ι a).1.mor = (show C.toGroupoidStr.morOn A from a.mor).1 ∧
          (S.subData hS.1 L).1.obj (ι a).1.src = (show A from L.1.obj a.src).1 ∧
          (S.subData hS.1 L').1.obj (ι a).1.tgt = (show A from L'.1.obj a.tgt).1 := by
  refine ⟨mem_subF_iff hS, fun L L' => ⟨S.subData_eq hS.1 L, ?_⟩⟩
  obtain ⟨hb, hl, hc⟩ := S.subInclOf_spec hS.1 L.1 L'.1 (S.subData hS.1 L) (S.subData hS.1 L')
    (S.subData_sub hS.1 L) (S.subData_sub hS.1 L') (S.subData_eq hS.1 L) (S.subData_eq hS.1 L')
  let ι : (subConstruction hS).Tr L L' → _ := S.subInclOf hS.1 L.1 L'.1 (S.subData hS.1 L)
    (S.subData hS.1 L') (S.subData_sub hS.1 L) (S.subData_sub hS.1 L') (S.subData_eq hS.1 L)
    (S.subData_eq hS.1 L')
  have hl' : ((subConstruction hS).transPolyfold L L').IsLocalScDiffeo
      (MPolyfold.subPolyfold
        (isSubMPolyfold_restrictTransSet (S.subData hS.1 L') (S.subData_sub hS.1 L))) ι := hl
  exact ⟨ι, hb, hl', (MPolyfold.subPolyfold_inclusion_isScSmooth _).comp hl'.isScSmoothMap, hc⟩

/-! ### Witness -/

section Witness

open EpGroupoid.Examples

/-- **The non-degenerate witness of Proposition 17.3.6**: for the subpolyfold `A = {0}` of
`C = ℤ/2 ⋉ ℝ`, `F_A(0)` contains the restricted uniformizer `Ψ_A`, whose group `ℤ/2` (the
isotropy of `0`) is nontrivial. -/
theorem reflection_subConstruction :
    ∃ L ∈ (subConstruction reflection_isSubpolyfold_zero.1).F
        (show ({0} : Set (Fin 1 → ℝ)) from ⟨0, rfl⟩),
      Nontrivial L.G ∧ Nonempty L.O := by
  refine ⟨_, (mem_subF_iff reflection_isSubpolyfold_zero.1 _ _).2
    ⟨_, reflection_isSubpolyfold_zero.2.2.1, rfl⟩, ?_, ?_⟩
  · refine nontrivial_of_ne (-1 : ℤˣ) 1 fun h => ?_
    have h' : ((-1 : ℤˣ) : ℤ) = ((1 : ℤˣ) : ℤ) := congrArg Units.val h
    rw [Units.val_neg, Units.val_one] at h'
    omega
  · exact ⟨⟨0, rfl⟩⟩

end Witness

end GCT.PolyfoldConstruction

end Polyfold
