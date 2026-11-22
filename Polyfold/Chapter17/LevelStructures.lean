import Polyfold.Chapter17.LevelOneCategory
import Polyfold.Chapter17.PolyfoldConstructionExamples

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.1 (p. 766): the polyfold structure `(F¹, M_{F¹})` of **Theorem 17.1.28**, **Corollary 17.1.29**,
and the levels `C^{i+1} := (C^i)¹`.  Numbers and pages are the 2021 text's.

# The polyfold `C¹` and the levels `C^i`

## The text, paraphrased

**2021 Theorem 17.1.28, p. 766**: the full subcategory `C_1` is a GCT `C¹` with the natural polyfold
structure `(F¹, M_{F¹})`: `F¹(α)` consists of the lifts `Ψ¹ : G ⋉ O¹ → C¹` of the `Ψ ∈ F(α)`, and
`M_{F¹}(Ψ¹, Ψ'¹) := (M(Ψ, Ψ'))¹` with the natural identification.
**2021 Corollary 17.1.29, p. 766**: if `C` satisfies (ZHOU), (SLUC) or (SLR), so does `C¹`.
**2021 p. 766**: `C^{i+1} := (C^i)¹`;
`|C_i|` has a natural metrizable topology.

## Main declarations

* `levelOneUnif hc Ψ`: the lifted uniformizer `Ψ¹` (the M-polyfold `O¹`, the induced action of
  `G`, the functor `levelOneFunctor Ψ` on the points of level `1`; full, faithful, injective on
  objects, and `|Ψ¹|` an open embedding, `isOpenEmbedding_levelOneFunctor`).
* `levelOneTransEquiv`: `M(Ψ¹, Ψ'¹) ≃ M(Ψ, Ψ')¹`; `ltrPolyfold`: `(M(Ψ, Ψ'))¹` on `M(Ψ¹, Ψ'¹)`;
  Definition 17.1.8 (a)–(c) at level `1`: `ltr_isLocalScDiffeo_src`, `ltr_isLocalScDiffeo_tgt`,
  `ltr_isScSmoothMap_unit`, `ltr_isScSmoothMap_inv`, `ltr_isScSmoothMap_mul` (through the local
  criterion `MPolyfold.isScSmoothOnFibredProduct_of_local`).
* **Theorem 17.1.28**: `levelOneF`,
  `levelOneConstruction hc : (S.levelOneGCT hc).PolyfoldConstruction`, `theorem_17_1_28`;
  `levelOne_hasRegularity_iff` (`C¹_m = C_{m+1}`), `levelOne_hasUniformizers`.
* **Corollary 17.1.29**: `levelOneModelFunctor` (`X_L → X_Ψ¹` for a covering family `L` of `F¹`),
  `isEquivalence_levelOneModelFunctor`, `isGeneralizedIso_levelOneModelHom`, `levelOneModel_iff`,
  `corollary_17_1_29_of_coveringFamily`, `corollary_17_1_29`.
* **`C^{i+1} := (C^i)¹`**: `GCT.UniformizedPolyfold` (a GCT with a polyfold structure and
  `F(α) ≠ ∅`), `UniformizedPolyfold.levelOne`, `level`, `levelIncl` (`C^i → C`),
  `hasRegularity_level_iff` (regularity shifted by `i`), `range_levelIncl_obj` (the objects of
  `C^i` are `C_i`), `bijective_orbitMap_levelEquivSub` (`|C^i| ≃ |C_i|`), `levelTopology`,
  `metrizableSpace_level` (`|C_i|` metrizable for all `i`), `levelTopology_one` (for `i = 1` the
  topology of Theorem 17.1.28), `level_spec`, `level_properties` (Corollary 17.1.29 for all `C^i`).

## Readings

* `F¹(α)` is the set of `Ψ¹` for `Ψ ∈ F(α)`, `α ∈ C_1`.  A lift `L = Ψ¹` need not determine `Ψ`;
  we read "`M_{F¹}(Ψ¹, Ψ'¹) := (M(Ψ, Ψ'))¹`" for one chosen `Ψ` with `L = Ψ¹` (`levelOneData`).
  The "natural identification" is `(q, φ, q') ↦ (q, φ, q')`, an sc-diffeomorphism
  (`levelOneInclOf_spec`, `theorem_17_1_28`).
* That `|Ψ¹| : |G ⋉ O¹| → |C¹|` is an open embedding (Definition 17.1.3 (3)) is left to the
  reader; it is `|Γ_Ψ¹| ∘ |O¹ → X¹|` for a covering family containing `Ψ`.
* (c) at level `1` is proved on sheets of `s` (Proposition 2.5.20) without identifying the index
  raise of the fibred product with the fibred product of the index raises.
* "`C¹` satisfies P" is Definition 17.1.22 for `(C¹, F¹, M_{F¹})`; it asks for a covering family of
  `F¹`.  For every covering family `L` of `F¹` the model `X_L` is equivalent to the full
  subcategory of `X_Ψ¹` on the components `O_λ¹` (`Ψ = (Ψ_λ) ⊔ c₀`), so it is generalized
  isomorphic to the index raise of a model of `C` (Propositions 7.4.8, 7.4.9 through
  `corollary_17_1_29_model`).  `corollary_17_1_29` is stated under `F(α) ≠ ∅` for all `α`
  (`HasUniformizers`), which gives a covering family of `F¹`.
* `C^{i+1} := (C^i)¹` presumes at each step a covering set of uniformizers (p. 752).  That the
  footprints of `F¹` cover `|C¹|` is not evident when only those of `F` cover `|C|` (the base
  points of the `Ψ ∈ F` need not have regularity `1`), so we iterate under `F(α) ≠ ∅` for all
  `α`, which passes to `F¹` (`levelOne_hasUniformizers`).  The natural topology of `|C_i|` is that
  of the GCT `C^i`, transported along the bijection `|C^i| → |C_i|`; for `i = 1` it is the
  topology transported from `|X_Ψ¹|` (`levelTopology_one`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology TopologicalSpace CategoryTheory

noncomputable section

universe u

namespace Polyfold

/-! ### Sc-smoothness on a fibred product, locally through the second factor -/

namespace MPolyfold

variable {A B Z D : Type u} [TopologicalSpace A] [T2Space A] [ParacompactSpace A]
  [TopologicalSpace B] [T2Space B] [ParacompactSpace B] [TopologicalSpace Z] [T2Space Z]
  [ParacompactSpace Z] [TopologicalSpace D] [T2Space D] [ParacompactSpace D]
  {PA : MPolyfold A} {PB : MPolyfold B} {PD : MPolyfold D} {PZ : MPolyfold Z}
  {f : A → Z} {g : B → Z} (hf : PA.IsLocalScDiffeo PZ f) (hg : PB.IsScSmoothMap PZ g)
  {h : fibredProduct f g → D}

/-- **A local criterion for Definition 17.1.8 (c)**: if near every point of `A ₓ×_g B` the map
`h` factors as `k ∘ pr₂` with `k` sc-smooth on an open set containing the second components,
then `h` is sc-smooth on the fibred product. -/
theorem isScSmoothOnFibredProduct_of_local
    (H : ∀ a₀ : fibredProduct f g, ∃ (N : Set (A × B)) (W : Set B) (k : B → D), IsOpen N ∧
      (a₀ : A × B) ∈ N ∧ PB.IsScSmoothOn PD k W ∧
      ∀ p : fibredProduct f g, (p : A × B) ∈ N → (p : A × B).2 ∈ W ∧ h p = k (p : A × B).2) :
    IsScSmoothOnFibredProduct PA PB PD hf hg h := by
  let _ := MPolyfold.paracompactSpace_prod PA PB
  let _ := (PA.prod PB).paracompactSpace_subtype (fibredProduct f g)
  have hA := isSubMPolyfold_fibredProduct hf hg
  change (subPolyfold hA).IsScSmoothMap PD h
  refine IsScSmoothOn.of_locally isOpen_univ fun a₀ _ => ?_
  obtain ⟨N, W, k, hN, ha₀, hk, hNk⟩ := H a₀
  have hNo : IsOpen (Subtype.val ⁻¹' N : Set (fibredProduct f g)) :=
    hN.preimage continuous_subtype_val
  have hsnd : (subPolyfold hA).IsScSmoothMap PB (fun p => (p : A × B).2) :=
    (isScSmoothMap_snd PA PB).comp (subPolyfold_inclusion_isScSmooth hA)
  refine ⟨Subtype.val ⁻¹' N, hNo, ha₀, subset_univ _, ?_⟩
  exact (IsScSmoothOn.comp hk (hsnd.mono hNo (subset_univ _)) fun p hp => (hNk p hp).1).congr
    fun p hp => (hNk p hp).2.symm

end MPolyfold

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} (S : C.PolyfoldConstruction)

omit S in
/-- The composition of a full subgroupoid on composable morphisms. -/
private theorem fullSub_comp_val_of {A : Set C.Obj} (φ ψ : C.toGroupoidStr.morOn A)
    (h : C.toGroupoidStr.src φ.1 = C.toGroupoidStr.tgt ψ.1) :
    ((C.toGroupoidStr.fullSub A).comp φ ψ : C.Mor) = C.toGroupoidStr.comp φ.1 ψ.1 := by
  simp only [GroupoidStr.fullSub, dif_pos h]

/-! ### The lifted uniformizer `Ψ¹ : G ⋉ O¹ → C¹` -/

section LiftUnif

variable (Ψ : S.Unif)

/-- The action of `G` on `O¹` (sc-smooth maps preserve the levels). -/
abbrev levelOneMulAction : MulAction Ψ.1.G (Ψ.1.P.Level 1) where
  smul g := MPolyfold.levelOneMap Ψ.1.P Ψ.1.P (fun y => g • y)
    ((Ψ.1.smooth_smul g).mapsTo_levelSet 1)
  one_smul x := MPolyfold.level_ext (one_smul Ψ.1.G (Ψ.1.P.levelVal 1 x))
  mul_smul g h x := MPolyfold.level_ext (mul_smul g h (Ψ.1.P.levelVal 1 x))

theorem levelVal_levelOneSmul (g : Ψ.1.G) (x : Ψ.1.P.Level 1) :
    letI := S.levelOneMulAction Ψ
    Ψ.1.P.levelVal 1 (g • x) = g • Ψ.1.P.levelVal 1 x := rfl

variable {S} in
/-- A point of `O¹` has regularity `1`. -/
theorem mem_regSet_obj (x : Ψ.1.P.Level 1) : Ψ.1.obj (Ψ.1.P.levelVal 1 x) ∈ S.regSet 1 :=
  (hasRegularity_iff Ψ (GroupoidStr.isomorphic_refl _ _) 1).2 (MPolyfold.levelVal_mem x)

/-- **The functor `Ψ¹ : G ⋉ O¹ → C_1`**: `Ψ` on the points of level `1`. -/
def levelOneFunctor :
    letI := S.levelOneMulAction Ψ
    GroupoidFunctor (GroupoidStr.translation Ψ.1.G (Ψ.1.P.Level 1)) (S.regSub 1) :=
  letI := S.levelOneMulAction Ψ
  { obj := fun x => ⟨Ψ.1.obj (Ψ.1.P.levelVal 1 x), mem_regSet_obj Ψ x⟩
    mor := fun p => ⟨Ψ.1.toUniformizer.mor (p.1, Ψ.1.P.levelVal 1 p.2), by
      rw [Ψ.1.toUniformizer.src_mor]; exact mem_regSet_obj Ψ p.2, by
      rw [Ψ.1.toUniformizer.tgt_mor]; exact mem_regSet_obj Ψ (p.1 • p.2)⟩
    src_mor := fun p => Subtype.ext (Ψ.1.toUniformizer.src_mor (p.1, Ψ.1.P.levelVal 1 p.2))
    tgt_mor := fun p => Subtype.ext (Ψ.1.toUniformizer.tgt_mor (p.1, Ψ.1.P.levelVal 1 p.2))
    mor_comp := fun p p' h => by
      refine Subtype.ext ?_
      have h' : (GroupoidStr.translation Ψ.1.G Ψ.1.O).src (p.1, Ψ.1.P.levelVal 1 p.2) =
          (GroupoidStr.translation Ψ.1.G Ψ.1.O).tgt (p'.1, Ψ.1.P.levelVal 1 p'.2) :=
        congrArg (Ψ.1.P.levelVal 1) h
      rw [fullSub_comp_val_of _ _ (by
        change C.toGroupoidStr.src (Ψ.1.toUniformizer.mor (p.1, Ψ.1.P.levelVal 1 p.2)) =
          C.toGroupoidStr.tgt (Ψ.1.toUniformizer.mor (p'.1, Ψ.1.P.levelVal 1 p'.2))
        rw [Ψ.1.toUniformizer.src_mor, Ψ.1.toUniformizer.tgt_mor]
        exact congrArg Ψ.1.obj h')]
      exact Ψ.1.functor.mor_comp (p.1, Ψ.1.P.levelVal 1 p.2) (p'.1, Ψ.1.P.levelVal 1 p'.2) h'
    mor_unit := fun x => Subtype.ext (Ψ.1.functor.mor_unit (Ψ.1.P.levelVal 1 x)) }

@[simp] theorem levelOneFunctor_obj_val (x : Ψ.1.P.Level 1) :
    ((S.levelOneFunctor Ψ).obj x).1 = Ψ.1.obj (Ψ.1.P.levelVal 1 x) := rfl

@[simp] theorem levelOneFunctor_mor_val (p : Ψ.1.G × Ψ.1.P.Level 1) :
    ((S.levelOneFunctor Ψ).mor p).1 = Ψ.1.toUniformizer.mor (p.1, Ψ.1.P.levelVal 1 p.2) := rfl

variable {S} in
/-- **`Ψ¹` is full**: every morphism of `C_1` between `Ψ(q)`, `Ψ(q')` is `Ψ(g, q)`. -/
theorem levelOneFunctor_full : (S.levelOneFunctor Ψ).toFunctor.Full := by
  let _ := S.levelOneMulAction Ψ
  refine (GroupoidFunctor.full_iff _).2 fun x x' ψ hs ht => ?_
  obtain ⟨g, hg, hψ⟩ := Ψ.1.toUniformizer.exists_smul_eq_mor (φ := ψ.1)
    (congrArg Subtype.val hs) (congrArg Subtype.val ht)
  exact ⟨(g, x), rfl, MPolyfold.level_ext hg, Subtype.ext hψ⟩

variable {S} in
theorem levelOneFunctor_faithful : (S.levelOneFunctor Ψ).toFunctor.Faithful := by
  let _ := S.levelOneMulAction Ψ
  refine (GroupoidFunctor.faithful_iff _).2 fun φ φ' hs _ he => ?_
  have h := Ψ.1.toUniformizer.mor_injective (congrArg Subtype.val he)
  exact Prod.ext (Prod.ext_iff.1 h).1 hs

variable {S} in
theorem injective_levelOneFunctor_obj : Injective (S.levelOneFunctor Ψ).obj := fun _ _ h =>
  MPolyfold.level_ext (Ψ.1.injective_obj (congrArg Subtype.val h))

end LiftUnif

/-! ### Covering families containing a given uniformizer -/

/-- The covering family `c` with one more uniformizer `Ψ` (index `Option ι`, `none ↦ Ψ`). -/
def CoveringFamily.adjoin (c : S.CoveringFamily) (Ψ : S.Unif) : S.CoveringFamily where
  ι := Option c.ι
  Ψ o := o.elim Ψ c.Ψ
  cover := eq_univ_of_forall fun z => by
    obtain ⟨i, hi⟩ := mem_iUnion.1 (c.cover.symm ▸ mem_univ z)
    exact mem_iUnion.2 ⟨some i, hi⟩

section OpenEmbedding

variable (hc : S.HasCoveringUniformizers) (Ψ : S.Unif)

/-- `O¹ → X¹` for the family with `Ψ` adjoined (the component `none`). -/
abbrev adjoinIncl : Ψ.1.P.Level 1 →
    (S.modelEP ((S.levelOneCover hc).adjoin S Ψ).Ψ).X.PObj.Level 1 :=
  MPolyfold.levelOneMap Ψ.1.P (S.modelEP ((S.levelOneCover hc).adjoin S Ψ).Ψ).X.PObj
    (Sigma.mk (β := fun o => (((S.levelOneCover hc).adjoin S Ψ).Ψ o).1.O) none)
    ((MPolyfold.isScSmoothMap_sigmaMk (fun o => (((S.levelOneCover hc).adjoin S Ψ).Ψ o).1.P)
      none).mapsTo_levelSet 1)

theorem isLocalScDiffeo_adjoinIncl :
    Ψ.1.P.shift.IsLocalScDiffeo (S.modelEP ((S.levelOneCover hc).adjoin S Ψ).Ψ).X.PObj.shift
      (S.adjoinIncl hc Ψ) :=
  (MPolyfold.isLocalScDiffeo_sigmaMk (fun o => (((S.levelOneCover hc).adjoin S Ψ).Ψ o).1.P)
    none).levelOne

theorem levelOneFunctor_orbitMap_π (x : Ψ.1.P.Level 1) :
    letI := S.levelOneMulAction Ψ
    (S.levelOneFunctor Ψ).orbitMap ((GroupoidStr.translation Ψ.1.G (Ψ.1.P.Level 1)).π x) =
      (S.modelFunctorOne ((S.levelOneCover hc).adjoin S Ψ).Ψ).orbitMap
        ((S.modelEP ((S.levelOneCover hc).adjoin S Ψ).Ψ).X.liftOne.π (S.adjoinIncl hc Ψ x)) :=
  rfl

/-- **`|Ψ¹| : |G ⋉ O¹| → |C¹|` is an open embedding** (Definition 17.1.3 (3) for `Ψ¹`): it is
`|Γ_Ψ¹| ∘ |O¹ → X¹|` for a covering family containing `Ψ`, `|Γ_Ψ¹|` a homeomorphism. -/
theorem isOpenEmbedding_levelOneFunctor :
    letI := S.levelOneMulAction Ψ
    @IsOpenEmbedding _ _ _ (S.levelOneTopology hc) (S.levelOneFunctor Ψ).orbitMap := by
  let _ := S.levelOneMulAction Ψ
  let _ := S.levelOneTopology hc
  set c := (S.levelOneCover hc).adjoin S Ψ
  have hΓ := S.isHomeomorph_modelOrbitEquivOne hc c
  have hX := (S.modelEP c.Ψ).X.liftOne.proposition_7_1_8_isOpenQuotientMap
  have hι := S.isLocalScDiffeo_adjoinIncl hc Ψ
  set T := GroupoidStr.translation Ψ.1.G (Ψ.1.P.Level 1)
  have hfac : (S.levelOneFunctor Ψ).orbitMap ∘ T.π =
      (S.modelFunctorOne c.Ψ).orbitMap ∘ (S.modelEP c.Ψ).X.liftOne.π ∘ S.adjoinIncl hc Ψ :=
    funext fun x => S.levelOneFunctor_orbitMap_π hc Ψ x
  have hcomp : Continuous ((S.modelFunctorOne c.Ψ).orbitMap ∘ (S.modelEP c.Ψ).X.liftOne.π ∘
      S.adjoinIncl hc Ψ) :=
    hΓ.continuous.comp (hX.continuous.comp hι.continuous)
  have hq : IsQuotientMap T.π := isQuotientMap_quotient_mk'
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_
  · exact hq.continuous_iff.2 (hfac ▸ hcomp)
  · intro a b h
    induction a using Quotient.inductionOn with | h x => ?_
    induction b using Quotient.inductionOn with | h y => ?_
    have h' : (S.regSub 1).π ((S.levelOneFunctor Ψ).obj x) =
        (S.regSub 1).π ((S.levelOneFunctor Ψ).obj y) := h
    obtain ⟨φ, hs, ht⟩ := GroupoidStr.isomorphic_fullSub_iff.1 (((S.regSub 1).π_eq_π_iff).1 h')
    obtain ⟨g, hg, -⟩ := Ψ.1.toUniformizer.exists_smul_eq_mor (φ := φ) hs ht
    exact (T.π_eq_π_iff).2 ⟨(g, x), rfl, MPolyfold.level_ext hg⟩
  · intro W hW
    have hW' : (S.levelOneFunctor Ψ).orbitMap '' W =
        ((S.modelFunctorOne c.Ψ).orbitMap ∘ (S.modelEP c.Ψ).X.liftOne.π ∘ S.adjoinIncl hc Ψ) ''
          (T.π ⁻¹' W) := by
      rw [← hfac, image_comp, image_preimage_eq _ hq.surjective]
    rw [hW', image_comp, image_comp]
    exact hΓ.isOpenMap _ (hX.isOpenMap _ (hι.isOpenMap _ (hW.preimage hq.continuous)))

end OpenEmbedding

/-- **The lifted uniformizer `Ψ¹ : G ⋉ O¹ → C¹`** (p. 766): the M-polyfold `O¹` (Part I's
`X¹`), the induced action of `G`, and the functor `Ψ` on the points of level `1`. -/
def levelOneUnif (hc : S.HasCoveringUniformizers) (Ψ : S.Unif) :
    (S.levelOneGCT hc).LocalUniformizer :=
  letI := S.levelOneMulAction Ψ
  { O := Ψ.1.P.Level 1
    P := Ψ.1.P.shift
    G := Ψ.1.G
    smooth_smul := fun g => MPolyfold.IsScSmoothMap.levelOne (Ψ.1.smooth_smul g) fun _ => rfl
    functor := S.levelOneFunctor Ψ
    injective_obj := injective_levelOneFunctor_obj Ψ
    full := levelOneFunctor_full Ψ
    faithful := levelOneFunctor_faithful Ψ
    isOpenEmbedding_orbitMap := S.isOpenEmbedding_levelOneFunctor hc Ψ }


/-! ### The transition sets `M(Ψ¹, Ψ'¹) = M(Ψ, Ψ')¹` -/

section Transition

variable (hc : S.HasCoveringUniformizers) (Ψ Ψ' : S.Unif)

variable {S Ψ Ψ'} in
theorem tr_mem_levelSet_iff (a : S.Tr Ψ Ψ') (m : ℕ) :
    a ∈ (S.transPolyfold Ψ Ψ').levelSet m ↔ a.src ∈ Ψ.1.P.levelSet m :=
  ((S.isLocalScDiffeo_trSrc Ψ Ψ').mem_levelSet_iff a m).symm

variable {S Ψ Ψ'} in
theorem tr_mem_levelSet_iff_tgt (a : S.Tr Ψ Ψ') (m : ℕ) :
    a ∈ (S.transPolyfold Ψ Ψ').levelSet m ↔ a.tgt ∈ Ψ'.1.P.levelSet m :=
  ((S.isLocalScDiffeo_trTgt Ψ Ψ').mem_levelSet_iff a m).symm

/-- **`M(Ψ¹, Ψ'¹) ≃ M(Ψ, Ψ')¹`** (p. 766, "with the natural identification"):
`(q, φ, q') ↦ (q, φ, q')`. -/
def levelOneTransEquiv :
    (S.levelOneUnif hc Ψ).Trans (S.levelOneUnif hc Ψ') ≃ (S.transPolyfold Ψ Ψ').Level 1 where
  toFun a := (S.transPolyfold Ψ Ψ').levelMk 1
    (S.toTr ⟨Ψ.1.P.levelVal 1 a.src, a.mor.1, Ψ'.1.P.levelVal 1 a.tgt,
      congrArg Subtype.val a.src_mor, congrArg Subtype.val a.tgt_mor⟩)
    ((tr_mem_levelSet_iff _ 1).2 (MPolyfold.levelVal_mem a.src))
  invFun b :=
    have hs := (tr_mem_levelSet_iff _ 1).1 (MPolyfold.levelVal_mem b)
    have ht := (tr_mem_levelSet_iff_tgt _ 1).1 (MPolyfold.levelVal_mem b)
    ⟨Ψ.1.P.levelMk 1 _ hs, ⟨((S.transPolyfold Ψ Ψ').levelVal 1 b).mor, by
        rw [((S.transPolyfold Ψ Ψ').levelVal 1 b).src_mor]
        exact mem_regSet_obj Ψ (Ψ.1.P.levelMk 1 _ hs), by
        rw [((S.transPolyfold Ψ Ψ').levelVal 1 b).tgt_mor]
        exact mem_regSet_obj Ψ' (Ψ'.1.P.levelMk 1 _ ht)⟩,
      Ψ'.1.P.levelMk 1 _ ht, Subtype.ext ((S.transPolyfold Ψ Ψ').levelVal 1 b).src_mor,
      Subtype.ext ((S.transPolyfold Ψ Ψ').levelVal 1 b).tgt_mor⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem levelOneTransEquiv_src (a) :
    ((S.transPolyfold Ψ Ψ').levelVal 1 (S.levelOneTransEquiv hc Ψ Ψ' a)).src =
      Ψ.1.P.levelVal 1 a.src := rfl

@[simp] theorem levelOneTransEquiv_mor (a) :
    ((S.transPolyfold Ψ Ψ').levelVal 1 (S.levelOneTransEquiv hc Ψ Ψ' a)).mor = a.mor.1 := rfl

@[simp] theorem levelOneTransEquiv_tgt (a) :
    ((S.transPolyfold Ψ Ψ').levelVal 1 (S.levelOneTransEquiv hc Ψ Ψ' a)).tgt =
      Ψ'.1.P.levelVal 1 a.tgt := rfl

/-- **The transition M-polyfold `M_{F¹}(Ψ¹, Ψ'¹)`** (a type synonym of the transition set carrying
the topology and the M-polyfold structure of `M(Ψ, Ψ')¹`). -/
def LTr : Type u := (S.levelOneUnif hc Ψ).Trans (S.levelOneUnif hc Ψ')

instance : TopologicalSpace (S.LTr hc Ψ Ψ') :=
  TopologicalSpace.induced (S.levelOneTransEquiv hc Ψ Ψ') inferInstance

/-- `M_{F¹}(Ψ¹, Ψ'¹) ≃ₜ M(Ψ, Ψ')¹`. -/
def ltrHomeomorph : S.LTr hc Ψ Ψ' ≃ₜ (S.transPolyfold Ψ Ψ').Level 1 :=
  Equiv.toHomeomorphOfIsInducing
    (S.levelOneTransEquiv hc Ψ Ψ' : S.LTr hc Ψ Ψ' ≃ (S.transPolyfold Ψ Ψ').Level 1) ⟨rfl⟩

instance : T2Space (S.LTr hc Ψ Ψ') := (S.ltrHomeomorph hc Ψ Ψ').isEmbedding.t2Space

instance : ParacompactSpace (S.LTr hc Ψ Ψ') :=
  (S.ltrHomeomorph hc Ψ Ψ').isClosedEmbedding.paracompactSpace

/-- **The M-polyfold `M_{F¹}(Ψ¹, Ψ'¹) := (M(Ψ, Ψ'))¹`** (p. 766): the index raise of
`M(Ψ, Ψ')` (Part I), transported along the natural identification. -/
def ltrPolyfold : MPolyfold (S.LTr hc Ψ Ψ') :=
  (S.transPolyfold Ψ Ψ').shift.transport (S.ltrHomeomorph hc Ψ Ψ').symm

theorem ltr_isLocalScDiffeo_homeomorph :
    (S.ltrPolyfold hc Ψ Ψ').IsLocalScDiffeo (S.transPolyfold Ψ Ψ').shift
      (S.ltrHomeomorph hc Ψ Ψ') := fun _ =>
  ⟨univ, univ, (S.ltrHomeomorph hc Ψ Ψ').symm, mem_univ _,
    ((S.transPolyfold Ψ Ψ').shift.isScDiffeoOn_transport (S.ltrHomeomorph hc Ψ Ψ').symm).symm⟩

theorem ltr_isScSmoothMap_homeomorph_symm :
    (S.transPolyfold Ψ Ψ').shift.IsScSmoothMap (S.ltrPolyfold hc Ψ Ψ')
      (S.ltrHomeomorph hc Ψ Ψ').symm :=
  ((S.transPolyfold Ψ Ψ').shift.isScDiffeoOn_transport (S.ltrHomeomorph hc Ψ Ψ').symm).isScSmoothOn

/-- An element of `M(Ψ¹, Ψ'¹)` as an element of the transition M-polyfold. -/
abbrev toLTr {Ψ Ψ' : S.Unif} (a : (S.levelOneUnif hc Ψ).Trans (S.levelOneUnif hc Ψ')) :
    S.LTr hc Ψ Ψ' := a

/-- **Definition 17.1.8 (a) for `(F¹, M_{F¹})`**: `s : M(Ψ¹, Ψ'¹) → O¹` is a local
sc-diffeomorphism (the index raise of `s`). -/
theorem ltr_isLocalScDiffeo_src :
    (S.ltrPolyfold hc Ψ Ψ').IsLocalScDiffeo (S.levelOneUnif hc Ψ).P
      fun a : S.LTr hc Ψ Ψ' => a.src :=
  (S.isLocalScDiffeo_trSrc Ψ Ψ').levelOne.comp (S.ltr_isLocalScDiffeo_homeomorph hc Ψ Ψ')

/-- **Definition 17.1.8 (a) for `(F¹, M_{F¹})`**: `t : M(Ψ¹, Ψ'¹) → O'¹` is a local
sc-diffeomorphism. -/
theorem ltr_isLocalScDiffeo_tgt :
    (S.ltrPolyfold hc Ψ Ψ').IsLocalScDiffeo (S.levelOneUnif hc Ψ').P
      fun a : S.LTr hc Ψ Ψ' => a.tgt :=
  (S.isLocalScDiffeo_trTgt Ψ Ψ').levelOne.comp (S.ltr_isLocalScDiffeo_homeomorph hc Ψ Ψ')

/-- **Definition 17.1.8 (b) for `(F¹, M_{F¹})`**: the unit map `O¹ → M(Ψ¹, Ψ¹)` is sc-smooth. -/
theorem ltr_isScSmoothMap_unit :
    (S.levelOneUnif hc Ψ).P.IsScSmoothMap (S.ltrPolyfold hc Ψ Ψ)
      fun q => S.toLTr hc (GroupoidStr.TransitionSet.unit q) :=
  (S.ltr_isScSmoothMap_homeomorph_symm hc Ψ Ψ).comp
    (MPolyfold.IsScSmoothMap.levelOne (f₁ := MPolyfold.levelOneMap Ψ.1.P (S.transPolyfold Ψ Ψ)
      (fun q => S.toTr (GroupoidStr.TransitionSet.unit q))
      ((S.isScSmoothMap_trUnit Ψ).mapsTo_levelSet 1)) (S.isScSmoothMap_trUnit Ψ) fun _ => rfl)

/-- **Definition 17.1.8 (b) for `(F¹, M_{F¹})`**: the inversion `M(Ψ¹, Ψ'¹) → M(Ψ'¹, Ψ¹)` is
sc-smooth. -/
theorem ltr_isScSmoothMap_inv :
    (S.ltrPolyfold hc Ψ Ψ').IsScSmoothMap (S.ltrPolyfold hc Ψ' Ψ)
      fun a : S.LTr hc Ψ Ψ' => S.toLTr hc (GroupoidStr.TransitionSet.inv a) :=
  (S.ltr_isScSmoothMap_homeomorph_symm hc Ψ' Ψ).comp
    ((MPolyfold.IsScSmoothMap.levelOne (f₁ := MPolyfold.levelOneMap (S.transPolyfold Ψ Ψ')
      (S.transPolyfold Ψ' Ψ) (fun a => S.toTr (GroupoidStr.TransitionSet.inv a))
      ((S.isScSmoothMap_trInv Ψ Ψ').mapsTo_levelSet 1)) (S.isScSmoothMap_trInv Ψ Ψ')
      fun _ => rfl).comp (S.ltr_isLocalScDiffeo_homeomorph hc Ψ Ψ').isScSmoothMap)

/-- **Definition 17.1.8 (c) for `(F¹, M_{F¹})`**: the multiplication
`M(Ψ'¹, Ψ''¹) ₛ×ₜ M(Ψ¹, Ψ'¹) → M(Ψ¹, Ψ''¹)` is sc-smooth.  Near a point, `b ↦ m(σ(t b), b)` for
a sheet `σ` of `s` on level `0` is sc-smooth (Definition 17.1.8 (c) for `M`), so is its index
raise (Part I), and the multiplication on level `1` is this raise composed with `pr₂`. -/
theorem ltr_isScSmoothMap_mul (Ψ'' : S.Unif) :
    MPolyfold.IsScSmoothOnFibredProduct (S.ltrPolyfold hc Ψ' Ψ'') (S.ltrPolyfold hc Ψ Ψ')
      (S.ltrPolyfold hc Ψ Ψ'') (S.ltr_isLocalScDiffeo_src hc Ψ' Ψ'')
      (S.ltr_isLocalScDiffeo_tgt hc Ψ Ψ').isScSmoothMap
      fun x => S.toLTr hc (GroupoidStr.TransitionSet.mul x) := by
  classical
  refine MPolyfold.isScSmoothOnFibredProduct_of_local _ _ fun a₀ => ?_
  set e₁ := S.ltrHomeomorph hc Ψ' Ψ''
  set e₂ := S.ltrHomeomorph hc Ψ Ψ'
  set e₃ := S.ltrHomeomorph hc Ψ Ψ''
  let v₁ : S.LTr hc Ψ' Ψ'' → S.Tr Ψ' Ψ'' := fun a => (S.transPolyfold Ψ' Ψ'').levelVal 1 (e₁ a)
  let v₂ : S.LTr hc Ψ Ψ' → S.Tr Ψ Ψ' := fun a => (S.transPolyfold Ψ Ψ').levelVal 1 (e₂ a)
  have hv₁ : Continuous v₁ := (MPolyfold.continuous_levelVal 1).comp e₁.continuous
  have hv₂ : Continuous v₂ := (MPolyfold.continuous_levelVal 1).comp e₂.continuous
  have hsrc : ∀ p : MPolyfold.fibredProduct (fun a : S.LTr hc Ψ' Ψ'' => a.src)
      (fun a : S.LTr hc Ψ Ψ' => a.tgt), (v₁ p.1.1).src = (v₂ p.1.2).tgt :=
    fun p => congrArg (Ψ'.1.P.levelVal 1) (show p.1.1.src = p.1.2.tgt from p.2)
  -- the sheet of `s` on level `0` at `v₁ a₀`
  obtain ⟨U, V, σ, hU, hd⟩ := S.isLocalScDiffeo_trSrc Ψ' Ψ'' (v₁ a₀.1.1)
  have hg₀ := (S.isLocalScDiffeo_trTgt Ψ Ψ').isScSmoothMap
  let _ := MPolyfold.paracompactSpace_prod (S.transPolyfold Ψ' Ψ'') (S.transPolyfold Ψ Ψ')
  let p₀ : MPolyfold.fibredProduct (fun a : S.Tr Ψ' Ψ'' => a.src) (fun a : S.Tr Ψ Ψ' => a.tgt) :=
    ⟨(v₁ a₀.1.1, v₂ a₀.1.2), hsrc a₀⟩
  let d := MPolyfold.fibredSubDataL hd hg₀
  let r : S.Tr Ψ Ψ' → MPolyfold.fibredProduct (fun a : S.Tr Ψ' Ψ'' => a.src)
      (fun a : S.Tr Ψ Ψ' => a.tgt) := fun b => d.retractInto p₀ (σ b.tgt, b)
  have hr : ∀ b : S.Tr Ψ Ψ', b.tgt ∈ V → (r b : S.Tr Ψ' Ψ'' × S.Tr Ψ Ψ') = (σ b.tgt, b) :=
    fun b hb => d.retractInto_val p₀ ⟨hd.mapsTo_inv hb, hb⟩
  let k₀ : S.Tr Ψ Ψ' → S.Tr Ψ Ψ'' := fun b => S.toTr (GroupoidStr.TransitionSet.mul (r b))
  have hk₀ : (S.transPolyfold Ψ Ψ').IsScSmoothOn (S.transPolyfold Ψ Ψ'') k₀
      ((fun b : S.Tr Ψ Ψ' => b.tgt) ⁻¹' V) :=
    (S.isScSmoothMap_trMul Ψ Ψ' Ψ'').isScSmoothOn_sheet hd p₀
  have hk₀src : ∀ b : S.Tr Ψ Ψ', b.tgt ∈ V → (k₀ b).src = b.src := fun b hb =>
    congrArg (fun q : S.Tr Ψ' Ψ'' × S.Tr Ψ Ψ' => q.2.src) (hr b hb)
  have hk₀1 : ∀ b : S.Tr Ψ Ψ', b.tgt ∈ V → b ∈ (S.transPolyfold Ψ Ψ').levelSet 1 →
      k₀ b ∈ (S.transPolyfold Ψ Ψ'').levelSet 1 := fun b hb hb1 => by
    rw [tr_mem_levelSet_iff, hk₀src b hb]
    exact (tr_mem_levelSet_iff b 1).1 hb1
  -- its index raise
  let k₁ : (S.transPolyfold Ψ Ψ').Level 1 → (S.transPolyfold Ψ Ψ'').Level 1 := fun x =>
    if hx : k₀ ((S.transPolyfold Ψ Ψ').levelVal 1 x) ∈ (S.transPolyfold Ψ Ψ'').levelSet 1 then
      (S.transPolyfold Ψ Ψ'').levelMk 1 _ hx
    else e₃ (S.toLTr hc (GroupoidStr.TransitionSet.mul a₀))
  have hk₁ := hk₀.levelOne (f₁ := k₁) fun x hx => by
    simp only [k₁, dif_pos (hk₀1 _ hx (MPolyfold.levelVal_mem x)), MPolyfold.levelVal_levelMk]
  let W : Set (S.LTr hc Ψ Ψ') := e₂ ⁻¹' {x | (S.transPolyfold Ψ Ψ').levelVal 1 x ∈
    (fun b : S.Tr Ψ Ψ' => b.tgt) ⁻¹' V}
  have hWo : IsOpen W := hk₁.isOpen.preimage e₂.continuous
  refine ⟨{p | v₁ p.1 ∈ U ∧ (v₂ p.2).tgt ∈ V}, W, e₃.symm ∘ k₁ ∘ e₂,
    (hd.isOpen_source.preimage (hv₁.comp continuous_fst)).inter
      (hd.isOpen_target.preimage ((S.continuous_trTgt Ψ Ψ').comp (hv₂.comp continuous_snd))),
    ⟨hU, (hsrc a₀).symm ▸ hd.mapsTo hU⟩, ?_, fun p hp => ⟨hp.2, ?_⟩⟩
  · exact MPolyfold.IsScSmoothOn.comp (S.ltr_isScSmoothMap_homeomorph_symm hc Ψ Ψ'')
      (MPolyfold.IsScSmoothOn.comp hk₁
        ((S.ltr_isLocalScDiffeo_homeomorph hc Ψ Ψ').isScSmoothMap.mono hWo (subset_univ _))
        fun x hx => hx) (mapsTo_univ _ _)
  · -- `m(a, b) = m(σ(t b), b)` for `a` in the sheet
    have hb : (v₂ p.1.2).tgt ∈ V := hp.2
    have hσ : σ (v₂ p.1.2).tgt = v₁ p.1.1 := by
      rw [← hsrc p, hd.left_inv _ hp.1]
    apply e₃.injective
    rw [Function.comp_apply, Function.comp_apply, e₃.apply_symm_apply]
    refine MPolyfold.level_ext ?_
    have h1 : k₀ ((S.transPolyfold Ψ Ψ').levelVal 1 (e₂ p.1.2)) ∈
        (S.transPolyfold Ψ Ψ'').levelSet 1 := hk₀1 _ hb (MPolyfold.levelVal_mem _)
    change _ = (S.transPolyfold Ψ Ψ'').levelVal 1 (dite _ _ _)
    rw [dif_pos h1, MPolyfold.levelVal_levelMk]
    have hrp := hr _ hb
    rw [hσ] at hrp
    refine GroupoidStr.TransitionSet.ext ?_ ?_ ?_
    · exact (congrArg (fun q : S.Tr Ψ' Ψ'' × S.Tr Ψ Ψ' => q.2.src) hrp).symm
    · change ((S.regSub 1).comp p.1.1.mor p.1.2.mor).1 = _
      rw [fullSub_comp_val_of _ _ (congrArg Subtype.val
        (GroupoidStr.TransitionSet.mor_composable_of_src_eq_tgt p.2))]
      exact (congrArg (fun q : S.Tr Ψ' Ψ'' × S.Tr Ψ Ψ' =>
        C.toGroupoidStr.comp q.1.mor q.2.mor) hrp).symm
    · exact (congrArg (fun q : S.Tr Ψ' Ψ'' × S.Tr Ψ Ψ' => q.1.tgt) hrp).symm

end Transition

/-! ### The polyfold structure `(F¹, M_{F¹})` -/

section Construction

variable (hc : S.HasCoveringUniformizers)

/-- **`F¹(α)`** (p. 766): the lifts `Ψ¹` of the `Ψ ∈ F(α)`. -/
def levelOneF (α : (S.levelOneGCT hc).Obj) : Set (S.levelOneGCT hc).LocalUniformizer :=
  {L | ∃ Ψ : S.Unif, Ψ.1 ∈ S.F (show S.regSet 1 from α).1 ∧ L = S.levelOneUnif hc Ψ}

variable {S} in
/-- `Ψ¹` is at `α` when `Ψ ∈ F(α)` and `α` has regularity `1`. -/
theorem levelOneUnif_isAt {α : (S.levelOneGCT hc).Obj} {Ψ : S.Unif}
    (hΨ : Ψ.1 ∈ S.F (show S.regSet 1 from α).1) : (S.levelOneUnif hc Ψ).IsAt α := by
  obtain ⟨q, hq⟩ := S.isAt _ Ψ.1 hΨ
  have hq1 : q ∈ Ψ.1.P.levelSet 1 := (regularity_eq_of_mem hΨ hq 1).1 (show S.regSet 1 from α).2
  exact ⟨Ψ.1.P.levelMk 1 q hq1, Subtype.ext hq⟩

theorem exists_levelOneData (L : GCT.Unif (S.levelOneF hc)) :
    ∃ Ψ : S.Unif, L.1 = S.levelOneUnif hc Ψ := by
  obtain ⟨L, α, Ψ, -, rfl⟩ := L
  exact ⟨Ψ, rfl⟩

/-- The uniformizer `Ψ ∈ F` chosen for `L ∈ F¹` with `L = Ψ¹`. -/
def levelOneData (L : GCT.Unif (S.levelOneF hc)) : S.Unif := (S.exists_levelOneData hc L).choose

theorem levelOneData_eq (L : GCT.Unif (S.levelOneF hc)) :
    L.1 = S.levelOneUnif hc (S.levelOneData hc L) :=
  (S.exists_levelOneData hc L).choose_spec

/-- The topology of `M(L, L')` for `L = Ψ¹`, `L' = Ψ'¹`. -/
@[instance_reducible]
def levelOneTopOf : ∀ (L L' : (S.levelOneGCT hc).LocalUniformizer) (Ψ Ψ' : S.Unif),
    L = S.levelOneUnif hc Ψ → L' = S.levelOneUnif hc Ψ' → TopologicalSpace (L.Trans L')
  | _, _, Ψ, Ψ', rfl, rfl => (inferInstance : TopologicalSpace (S.LTr hc Ψ Ψ'))

theorem levelOneT2Of : ∀ (L L' : (S.levelOneGCT hc).LocalUniformizer) (Ψ Ψ' : S.Unif)
    (h : L = S.levelOneUnif hc Ψ) (h' : L' = S.levelOneUnif hc Ψ'),
    @T2Space (L.Trans L') (S.levelOneTopOf hc L L' Ψ Ψ' h h')
  | _, _, Ψ, Ψ', rfl, rfl => (inferInstance : T2Space (S.LTr hc Ψ Ψ'))

theorem levelOneParaOf : ∀ (L L' : (S.levelOneGCT hc).LocalUniformizer) (Ψ Ψ' : S.Unif)
    (h : L = S.levelOneUnif hc Ψ) (h' : L' = S.levelOneUnif hc Ψ'),
    @ParacompactSpace (L.Trans L') (S.levelOneTopOf hc L L' Ψ Ψ' h h')
  | _, _, Ψ, Ψ', rfl, rfl => (inferInstance : ParacompactSpace (S.LTr hc Ψ Ψ'))

/-- The M-polyfold `M(L, L')` for `L = Ψ¹`, `L' = Ψ'¹`: `ltrPolyfold`, i.e. `M(Ψ, Ψ')¹`. -/
def levelOneMOf : ∀ (L L' : (S.levelOneGCT hc).LocalUniformizer) (Ψ Ψ' : S.Unif)
    (h : L = S.levelOneUnif hc Ψ) (h' : L' = S.levelOneUnif hc Ψ'),
    @MPolyfold (L.Trans L') (S.levelOneTopOf hc L L' Ψ Ψ' h h')
      (S.levelOneT2Of hc L L' Ψ Ψ' h h') (S.levelOneParaOf hc L L' Ψ Ψ' h h')
  | _, _, Ψ, Ψ', rfl, rfl => S.ltrPolyfold hc Ψ Ψ'

/-- The identification `M(L, L') → M(Ψ, Ψ')¹` for `L = Ψ¹`, `L' = Ψ'¹`. -/
def levelOneInclOf : ∀ (L L' : (S.levelOneGCT hc).LocalUniformizer) (Ψ Ψ' : S.Unif),
    L = S.levelOneUnif hc Ψ → L' = S.levelOneUnif hc Ψ' →
    L.Trans L' → (S.transPolyfold Ψ Ψ').Level 1
  | _, _, Ψ, Ψ', rfl, rfl => S.levelOneTransEquiv hc Ψ Ψ'

theorem levelOneSrcOf : ∀ (L L' : (S.levelOneGCT hc).LocalUniformizer) (Ψ Ψ' : S.Unif)
    (h : L = S.levelOneUnif hc Ψ) (h' : L' = S.levelOneUnif hc Ψ'),
    letI := S.levelOneTopOf hc L L' Ψ Ψ' h h'
    letI := S.levelOneT2Of hc L L' Ψ Ψ' h h'
    letI := S.levelOneParaOf hc L L' Ψ Ψ' h h'
    (S.levelOneMOf hc L L' Ψ Ψ' h h').IsLocalScDiffeo L.P GroupoidStr.TransitionSet.src
  | _, _, Ψ, Ψ', rfl, rfl => S.ltr_isLocalScDiffeo_src hc Ψ Ψ'

theorem levelOneTgtOf : ∀ (L L' : (S.levelOneGCT hc).LocalUniformizer) (Ψ Ψ' : S.Unif)
    (h : L = S.levelOneUnif hc Ψ) (h' : L' = S.levelOneUnif hc Ψ'),
    letI := S.levelOneTopOf hc L L' Ψ Ψ' h h'
    letI := S.levelOneT2Of hc L L' Ψ Ψ' h h'
    letI := S.levelOneParaOf hc L L' Ψ Ψ' h h'
    (S.levelOneMOf hc L L' Ψ Ψ' h h').IsLocalScDiffeo L'.P GroupoidStr.TransitionSet.tgt
  | _, _, Ψ, Ψ', rfl, rfl => S.ltr_isLocalScDiffeo_tgt hc Ψ Ψ'

theorem levelOneUnitOf : ∀ (L : (S.levelOneGCT hc).LocalUniformizer) (Ψ : S.Unif)
    (h : L = S.levelOneUnif hc Ψ),
    letI := S.levelOneTopOf hc L L Ψ Ψ h h
    letI := S.levelOneT2Of hc L L Ψ Ψ h h
    letI := S.levelOneParaOf hc L L Ψ Ψ h h
    L.P.IsScSmoothMap (S.levelOneMOf hc L L Ψ Ψ h h) GroupoidStr.TransitionSet.unit
  | _, Ψ, rfl => S.ltr_isScSmoothMap_unit hc Ψ

theorem levelOneInvOf : ∀ (L L' : (S.levelOneGCT hc).LocalUniformizer) (Ψ Ψ' : S.Unif)
    (h : L = S.levelOneUnif hc Ψ) (h' : L' = S.levelOneUnif hc Ψ'),
    letI := S.levelOneTopOf hc L L' Ψ Ψ' h h'
    letI := S.levelOneT2Of hc L L' Ψ Ψ' h h'
    letI := S.levelOneParaOf hc L L' Ψ Ψ' h h'
    letI := S.levelOneTopOf hc L' L Ψ' Ψ h' h
    letI := S.levelOneT2Of hc L' L Ψ' Ψ h' h
    letI := S.levelOneParaOf hc L' L Ψ' Ψ h' h
    (S.levelOneMOf hc L L' Ψ Ψ' h h').IsScSmoothMap (S.levelOneMOf hc L' L Ψ' Ψ h' h)
      GroupoidStr.TransitionSet.inv
  | _, _, Ψ, Ψ', rfl, rfl => S.ltr_isScSmoothMap_inv hc Ψ Ψ'

theorem levelOneMulOf : ∀ (L L' L'' : (S.levelOneGCT hc).LocalUniformizer) (Ψ Ψ' Ψ'' : S.Unif)
    (h : L = S.levelOneUnif hc Ψ) (h' : L' = S.levelOneUnif hc Ψ')
    (h'' : L'' = S.levelOneUnif hc Ψ''),
    letI := S.levelOneTopOf hc L' L'' Ψ' Ψ'' h' h''
    letI := S.levelOneT2Of hc L' L'' Ψ' Ψ'' h' h''
    letI := S.levelOneParaOf hc L' L'' Ψ' Ψ'' h' h''
    letI := S.levelOneTopOf hc L L' Ψ Ψ' h h'
    letI := S.levelOneT2Of hc L L' Ψ Ψ' h h'
    letI := S.levelOneParaOf hc L L' Ψ Ψ' h h'
    letI := S.levelOneTopOf hc L L'' Ψ Ψ'' h h''
    letI := S.levelOneT2Of hc L L'' Ψ Ψ'' h h''
    letI := S.levelOneParaOf hc L L'' Ψ Ψ'' h h''
    MPolyfold.IsScSmoothOnFibredProduct (S.levelOneMOf hc L' L'' Ψ' Ψ'' h' h'')
      (S.levelOneMOf hc L L' Ψ Ψ' h h') (S.levelOneMOf hc L L'' Ψ Ψ'' h h'')
      (S.levelOneSrcOf hc L' L'' Ψ' Ψ'' h' h'')
      (S.levelOneTgtOf hc L L' Ψ Ψ' h h').isScSmoothMap GroupoidStr.TransitionSet.mul
  | _, _, _, Ψ, Ψ', Ψ'', rfl, rfl, rfl => S.ltr_isScSmoothMap_mul hc Ψ Ψ' Ψ''

/-- The identification `M(L, L') ≃ M(Ψ, Ψ')¹` is bijective, an sc-diffeomorphism, and keeps the
points and the morphism. -/
theorem levelOneInclOf_spec : ∀ (L L' : (S.levelOneGCT hc).LocalUniformizer) (Ψ Ψ' : S.Unif)
    (h : L = S.levelOneUnif hc Ψ) (h' : L' = S.levelOneUnif hc Ψ'),
    letI := S.levelOneTopOf hc L L' Ψ Ψ' h h'
    letI := S.levelOneT2Of hc L L' Ψ Ψ' h h'
    letI := S.levelOneParaOf hc L L' Ψ Ψ' h h'
    Bijective (S.levelOneInclOf hc L L' Ψ Ψ' h h') ∧
      (S.levelOneMOf hc L L' Ψ Ψ' h h').IsLocalScDiffeo (S.transPolyfold Ψ Ψ').shift
        (S.levelOneInclOf hc L L' Ψ Ψ' h h') ∧
      ∀ a : L.Trans L',
        ((S.transPolyfold Ψ Ψ').levelVal 1 (S.levelOneInclOf hc L L' Ψ Ψ' h h' a)).mor =
          (show C.toGroupoidStr.morOn (S.regSet 1) from a.mor).1 ∧
        Ψ.1.obj ((S.transPolyfold Ψ Ψ').levelVal 1 (S.levelOneInclOf hc L L' Ψ Ψ' h h' a)).src =
          (show S.regSet 1 from L.obj a.src).1 ∧
        Ψ'.1.obj ((S.transPolyfold Ψ Ψ').levelVal 1 (S.levelOneInclOf hc L L' Ψ Ψ' h h' a)).tgt =
          (show S.regSet 1 from L'.obj a.tgt).1
  | _, _, Ψ, Ψ', rfl, rfl =>
    ⟨(S.levelOneTransEquiv hc Ψ Ψ').bijective, S.ltr_isLocalScDiffeo_homeomorph hc Ψ Ψ',
      fun _ => ⟨rfl, rfl, rfl⟩⟩

/-- **2021 Theorem 17.1.28, p. 766, the polyfold structure `(F¹, M_{F¹})` on `C¹`**:
`F¹(α)` consists of the lifts `Ψ¹ : G ⋉ O¹ → C¹` of the `Ψ ∈ F(α)`, and
`M_{F¹}(Ψ¹, Ψ'¹) := (M(Ψ, Ψ'))¹` with the natural identification (for the chosen
`Ψ = levelOneData L` with `L = Ψ¹`). -/
def levelOneConstruction : (S.levelOneGCT hc).PolyfoldConstruction where
  F := S.levelOneF hc
  isAt α L hL := by
    obtain ⟨Ψ, hΨ, rfl⟩ := hL
    exact levelOneUnif_isAt hc hΨ
  topM L L' := S.levelOneTopOf hc L.1 L'.1 (S.levelOneData hc L) (S.levelOneData hc L')
    (S.levelOneData_eq hc L) (S.levelOneData_eq hc L')
  t2M L L' := S.levelOneT2Of hc L.1 L'.1 (S.levelOneData hc L) (S.levelOneData hc L')
    (S.levelOneData_eq hc L) (S.levelOneData_eq hc L')
  paraM L L' := S.levelOneParaOf hc L.1 L'.1 (S.levelOneData hc L) (S.levelOneData hc L')
    (S.levelOneData_eq hc L) (S.levelOneData_eq hc L')
  M L L' := S.levelOneMOf hc L.1 L'.1 (S.levelOneData hc L) (S.levelOneData hc L')
    (S.levelOneData_eq hc L) (S.levelOneData_eq hc L')
  isLocalScDiffeo_src L L' := S.levelOneSrcOf hc L.1 L'.1 (S.levelOneData hc L)
    (S.levelOneData hc L') (S.levelOneData_eq hc L) (S.levelOneData_eq hc L')
  isLocalScDiffeo_tgt L L' := S.levelOneTgtOf hc L.1 L'.1 (S.levelOneData hc L)
    (S.levelOneData hc L') (S.levelOneData_eq hc L) (S.levelOneData_eq hc L')
  isScSmoothMap_unit L := S.levelOneUnitOf hc L.1 (S.levelOneData hc L) (S.levelOneData_eq hc L)
  isScSmoothMap_inv L L' := S.levelOneInvOf hc L.1 L'.1 (S.levelOneData hc L)
    (S.levelOneData hc L') (S.levelOneData_eq hc L) (S.levelOneData_eq hc L')
  isScSmoothMap_mul L L' L'' := S.levelOneMulOf hc L.1 L'.1 L''.1 (S.levelOneData hc L)
    (S.levelOneData hc L') (S.levelOneData hc L'') (S.levelOneData_eq hc L)
    (S.levelOneData_eq hc L') (S.levelOneData_eq hc L'')

end Construction

/-! ### Points of `Ψ¹` and the theorem -/

section Points

variable (hc : S.HasCoveringUniformizers)

/-- The identification `O_L = O¹` of a lift `L = Ψ¹`. -/
def levelOneObjCast : ∀ (L : (S.levelOneGCT hc).LocalUniformizer) (Ψ : S.Unif),
    L = S.levelOneUnif hc Ψ → L.O → Ψ.1.P.Level 1
  | _, _, rfl => id

/-- `O_L = O¹` is bijective, a local sc-diffeomorphism `O_L → O¹`, and keeps the points of `C`. -/
theorem levelOneObjCast_spec : ∀ (L : (S.levelOneGCT hc).LocalUniformizer) (Ψ : S.Unif)
    (h : L = S.levelOneUnif hc Ψ),
    Bijective (S.levelOneObjCast hc L Ψ h) ∧
      L.P.IsLocalScDiffeo Ψ.1.P.shift (S.levelOneObjCast hc L Ψ h) ∧
      ∀ x, Ψ.1.obj (Ψ.1.P.levelVal 1 (S.levelOneObjCast hc L Ψ h x)) =
        (show S.regSet 1 from L.obj x).1
  | _, _, rfl => ⟨bijective_id, MPolyfold.isLocalScDiffeo_id, fun _ => rfl⟩

variable {S hc} in
/-- A point of `O_L` is of level `m` iff its image in `O` is of level `m + 1`. -/
theorem levelOneObjCast_mem_levelSet_iff {L : (S.levelOneGCT hc).LocalUniformizer} {Ψ : S.Unif}
    (h : L = S.levelOneUnif hc Ψ) (x : L.O) (m : ℕ) :
    x ∈ L.P.levelSet m ↔
      Ψ.1.P.levelVal 1 (S.levelOneObjCast hc L Ψ h x) ∈ Ψ.1.P.levelSet (m + 1) :=
  ((S.levelOneObjCast_spec hc L Ψ h).2.1.mem_levelSet_iff x m).symm.trans
    (MPolyfold.mem_shift_levelSet_iff _)

variable {S hc} in
/-- **The regularity of `C¹` is that of `C` shifted by one** (`(O¹)_m = O_{m+1}`): an object
`α` of `C¹` in the footprint of a uniformizer of `F¹` has regularity `m` in `C¹` iff it has
regularity `m + 1` in `C`. -/
theorem levelOne_hasRegularity_iff (L : GCT.Unif (S.levelOneF hc)) {x : L.1.O}
    {α : (S.levelOneGCT hc).Obj}
    (hx : (S.levelOneGCT hc).toGroupoidStr.Isomorphic (L.1.obj x) α) (m : ℕ) :
    (S.levelOneConstruction hc).HasRegularity m α ↔ S.HasRegularity (m + 1) α.1 := by
  set Ψ := S.levelOneData hc L
  have hL := S.levelOneData_eq hc L
  rw [hasRegularity_iff (S := S.levelOneConstruction hc) L hx m,
    levelOneObjCast_mem_levelSet_iff hL x m]
  have hiso : C.toGroupoidStr.Isomorphic
      (Ψ.1.obj (Ψ.1.P.levelVal 1 (S.levelOneObjCast hc L.1 Ψ hL x))) α.1 := by
    rw [(S.levelOneObjCast_spec hc L.1 Ψ hL).2.2 x]
    exact GroupoidStr.isomorphic_fullSub_iff.1 hx
  exact (hasRegularity_iff Ψ hiso (m + 1)).symm

variable {S} in
/-- **`F¹(α) ≠ ∅`** for every object `α` of `C¹` when `F(α) ≠ ∅` for every `α`. -/
theorem levelOne_hasUniformizers (hu : S.HasUniformizers) :
    (S.levelOneConstruction (S.hasCoveringUniformizers_of_hasUniformizers hu)).HasUniformizers := by
  intro α
  obtain ⟨Ψ, hΨ⟩ := hu (show S.regSet 1 from α).1
  exact ⟨_, ⟨⟨Ψ, _, hΨ⟩, hΨ, rfl⟩⟩

variable {S} in
/-- Under `F(α) ≠ ∅` for all `α`: **`C¹_m = C_{m+1}`** on the objects of `C¹`. -/
theorem levelOne_hasRegularity_iff_of_hasUniformizers (hu : S.HasUniformizers)
    (α : (S.levelOneGCT (S.hasCoveringUniformizers_of_hasUniformizers hu)).Obj) (m : ℕ) :
    (S.levelOneConstruction (S.hasCoveringUniformizers_of_hasUniformizers hu)).HasRegularity m α ↔
      S.HasRegularity (m + 1) α.1 := by
  obtain ⟨L, hL⟩ := levelOne_hasUniformizers hu α
  obtain ⟨x, hx⟩ := (S.levelOneConstruction _).isAt α L hL
  subst hx
  exact levelOne_hasRegularity_iff ⟨L, _, hL⟩ (GroupoidStr.isomorphic_refl _ _) m

/-- **2021 Theorem 17.1.28, p. 766**: the full subcategory `C_1` is a GCT `C¹`
(`theorem_17_1_28_gct`) with the polyfold structure `(F¹, M_{F¹})`: `F¹(α)` consists of the lifts
`Ψ¹ : G ⋉ O¹ → C¹` of the `Ψ ∈ F(α)`, and for `L = Ψ¹`, `L' = Ψ'¹` the M-polyfold `M_{F¹}(L, L')`
is `M(Ψ, Ψ')¹` with the natural identification `(q, φ, q') ↦ (q, φ, q')`, an sc-diffeomorphism.
We read "`M_{F¹}(Ψ¹, Ψ'¹) := (M(Ψ, Ψ'))¹`" for one chosen `Ψ` with `L = Ψ¹` (`levelOneData`;
`Ψ¹` need not determine `Ψ`). -/
theorem theorem_17_1_28 :
    (S.levelOneGCT hc).toGroupoidStr = S.regSub 1 ∧
      (∀ α, (S.levelOneConstruction hc).F α =
        {L | ∃ Ψ : S.Unif, Ψ.1 ∈ S.F (show S.regSet 1 from α).1 ∧ L = S.levelOneUnif hc Ψ}) ∧
      (∀ Ψ : S.Unif, (S.levelOneUnif hc Ψ).O = Ψ.1.P.Level 1 ∧
        HEq (S.levelOneUnif hc Ψ).P Ψ.1.P.shift ∧
        ∀ x : Ψ.1.P.Level 1, (show S.regSet 1 from (S.levelOneUnif hc Ψ).obj x).1 =
          Ψ.1.obj (Ψ.1.P.levelVal 1 x)) ∧
      ∀ L L' : (S.levelOneConstruction hc).Unif,
        ∃ (Ψ Ψ' : S.Unif) (e : L.1.Trans L'.1 → (S.transPolyfold Ψ Ψ').Level 1),
          L.1 = S.levelOneUnif hc Ψ ∧ L'.1 = S.levelOneUnif hc Ψ' ∧ Bijective e ∧
          ((S.levelOneConstruction hc).transPolyfold L L').IsLocalScDiffeo
            (S.transPolyfold Ψ Ψ').shift e ∧
          ∀ a : L.1.Trans L'.1,
            ((S.transPolyfold Ψ Ψ').levelVal 1 (e a)).mor =
              (show C.toGroupoidStr.morOn (S.regSet 1) from a.mor).1 ∧
            Ψ.1.obj ((S.transPolyfold Ψ Ψ').levelVal 1 (e a)).src =
              (show S.regSet 1 from L.1.obj a.src).1 ∧
            Ψ'.1.obj ((S.transPolyfold Ψ Ψ').levelVal 1 (e a)).tgt =
              (show S.regSet 1 from L'.1.obj a.tgt).1 := by
  refine ⟨rfl, fun _ => rfl, fun _ => ⟨rfl, HEq.rfl, fun _ => rfl⟩, fun L L' => ?_⟩
  obtain ⟨h1, h2, h3⟩ := S.levelOneInclOf_spec hc L.1 L'.1 (S.levelOneData hc L)
    (S.levelOneData hc L') (S.levelOneData_eq hc L) (S.levelOneData_eq hc L')
  exact ⟨_, _, _, S.levelOneData_eq hc L, S.levelOneData_eq hc L', h1, h2, h3⟩

end Points

/-! ### Corollary 17.1.29: the models of `C¹` and the index raise of the models of `C` -/

/-- A morphism of the model `X_Ψ` is determined by its source, its target and its morphism of
`C`. -/
theorem modelMor_ext {ι : Type u} {Ψ : ι → S.Unif} {φ φ' : S.ModelMor Ψ}
    (hs : (S.modelGroupoid Ψ).src φ = (S.modelGroupoid Ψ).src φ')
    (ht : (S.modelGroupoid Ψ).tgt φ = (S.modelGroupoid Ψ).tgt φ') (hm : φ.2.mor = φ'.2.mor) :
    φ = φ' :=
  (S.modelMorEquiv Ψ).injective (GroupoidStr.TransitionSet.ext hs hm ht)

section ModelLevelOne

variable (hc : S.HasCoveringUniformizers) (L : (S.levelOneConstruction hc).CoveringFamily)
  (c₀ : S.CoveringFamily)

/-- The uniformizer `Ψ_λ` of `F` chosen for `L_λ = Ψ_λ¹`. -/
abbrev lData (i : L.ι) : S.Unif := S.levelOneData hc (L.Ψ i)

/-- **The covering family `(Ψ_λ)_λ ⊔ c₀`** of `F`, `L_λ = Ψ_λ¹` (`c₀` covers `|C|`). -/
def levelOneModelFamily : S.CoveringFamily where
  ι := L.ι ⊕ c₀.ι
  Ψ := Sum.elim (S.lData hc L) c₀.Ψ
  cover := eq_univ_of_forall fun z => by
    obtain ⟨i, hi⟩ := mem_iUnion.1 (c₀.cover.symm ▸ mem_univ z)
    exact mem_iUnion.2 ⟨Sum.inr i, hi⟩

/-- `O_λ¹ → X¹` for the family `levelOneModelFamily` (the component `inl λ`). -/
abbrev lObjIncl (i : L.ι) : (S.lData hc L i).1.P.Level 1 →
    (S.modelEP (S.levelOneModelFamily hc L c₀).Ψ).X.PObj.Level 1 :=
  MPolyfold.levelOneMap (S.lData hc L i).1.P (S.modelEP (S.levelOneModelFamily hc L c₀).Ψ).X.PObj
    (Sigma.mk (β := fun k => ((S.levelOneModelFamily hc L c₀).Ψ k).1.O) (Sum.inl i))
    ((MPolyfold.isScSmoothMap_sigmaMk (fun k => ((S.levelOneModelFamily hc L c₀).Ψ k).1.P)
      (Sum.inl i)).mapsTo_levelSet 1)

theorem isLocalScDiffeo_lObjIncl (i : L.ι) :
    (S.lData hc L i).1.P.shift.IsLocalScDiffeo
      (S.modelEP (S.levelOneModelFamily hc L c₀).Ψ).X.PObj.shift (S.lObjIncl hc L c₀ i) :=
  (MPolyfold.isLocalScDiffeo_sigmaMk (fun k => ((S.levelOneModelFamily hc L c₀).Ψ k).1.P)
    (Sum.inl i)).levelOne

/-- `M(Ψ_λ, Ψ_μ)¹ → 𝐗¹` for the family `levelOneModelFamily`. -/
abbrev lMorIncl (i j : L.ι) : (S.transPolyfold (S.lData hc L i) (S.lData hc L j)).Level 1 →
    (S.modelEP (S.levelOneModelFamily hc L c₀).Ψ).X.PMor.Level 1 :=
  MPolyfold.levelOneMap (S.transPolyfold (S.lData hc L i) (S.lData hc L j))
    (S.modelEP (S.levelOneModelFamily hc L c₀).Ψ).X.PMor
    (Sigma.mk (β := fun p : _ × _ => S.Tr ((S.levelOneModelFamily hc L c₀).Ψ p.1)
      ((S.levelOneModelFamily hc L c₀).Ψ p.2)) (Sum.inl i, Sum.inl j))
    ((MPolyfold.isScSmoothMap_sigmaMk (fun p : _ × _ => S.transPolyfold
      ((S.levelOneModelFamily hc L c₀).Ψ p.1) ((S.levelOneModelFamily hc L c₀).Ψ p.2))
      (Sum.inl i, Sum.inl j)).mapsTo_levelSet 1)

theorem isLocalScDiffeo_lMorIncl (i j : L.ι) :
    (S.transPolyfold (S.lData hc L i) (S.lData hc L j)).shift.IsLocalScDiffeo
      (S.modelEP (S.levelOneModelFamily hc L c₀).Ψ).X.PMor.shift (S.lMorIncl hc L c₀ i j) :=
  (MPolyfold.isLocalScDiffeo_sigmaMk (fun p : _ × _ => S.transPolyfold
      ((S.levelOneModelFamily hc L c₀).Ψ p.1) ((S.levelOneModelFamily hc L c₀).Ψ p.2))
    (Sum.inl i, Sum.inl j)).levelOne

/-- `O_{L_λ} = O_λ¹`. -/
abbrev lCast (i : L.ι) : (L.Ψ i).1.O → (S.lData hc L i).1.P.Level 1 :=
  S.levelOneObjCast hc (L.Ψ i).1 (S.lData hc L i) (S.levelOneData_eq hc (L.Ψ i))

/-- `M(L_λ, L_μ) = M(Ψ_λ, Ψ_μ)¹`. -/
abbrev lTrCast (i j : L.ι) :
    (L.Ψ i).1.Trans (L.Ψ j).1 → (S.transPolyfold (S.lData hc L i) (S.lData hc L j)).Level 1 :=
  S.levelOneInclOf hc (L.Ψ i).1 (L.Ψ j).1 (S.lData hc L i) (S.lData hc L j)
    (S.levelOneData_eq hc (L.Ψ i)) (S.levelOneData_eq hc (L.Ψ j))

theorem isLocalScDiffeo_lTrCast (i j : L.ι) :
    ((S.levelOneConstruction hc).transPolyfold (L.Ψ i) (L.Ψ j)).IsLocalScDiffeo
      (S.transPolyfold (S.lData hc L i) (S.lData hc L j)).shift (S.lTrCast hc L i j) :=
  (S.levelOneInclOf_spec hc (L.Ψ i).1 (L.Ψ j).1 _ _ (S.levelOneData_eq hc (L.Ψ i))
    (S.levelOneData_eq hc (L.Ψ j))).2.1

theorem isLocalScDiffeo_lCast (i : L.ι) :
    (L.Ψ i).1.P.IsLocalScDiffeo (S.lData hc L i).1.P.shift (S.lCast hc L i) :=
  (S.levelOneObjCast_spec hc _ _ (S.levelOneData_eq hc (L.Ψ i))).2.1

theorem lTrCast_spec (i j : L.ι) (a : (L.Ψ i).1.Trans (L.Ψ j).1) :
    ((S.transPolyfold _ _).levelVal 1 (S.lTrCast hc L i j a)).src =
        (S.lData hc L i).1.P.levelVal 1 (S.lCast hc L i a.src) ∧
      ((S.transPolyfold _ _).levelVal 1 (S.lTrCast hc L i j a)).tgt =
        (S.lData hc L j).1.P.levelVal 1 (S.lCast hc L j a.tgt) ∧
      ((S.transPolyfold _ _).levelVal 1 (S.lTrCast hc L i j a)).mor =
        (show C.toGroupoidStr.morOn (S.regSet 1) from a.mor).1 := by
  obtain ⟨-, -, h⟩ := S.levelOneInclOf_spec hc (L.Ψ i).1 (L.Ψ j).1 (S.lData hc L i)
    (S.lData hc L j) (S.levelOneData_eq hc (L.Ψ i)) (S.levelOneData_eq hc (L.Ψ j))
  obtain ⟨hm, hs, ht⟩ := h a
  exact ⟨(S.lData hc L i).1.injective_obj (hs.trans
      ((S.levelOneObjCast_spec hc _ _ (S.levelOneData_eq hc (L.Ψ i))).2.2 a.src).symm),
    (S.lData hc L j).1.injective_obj (ht.trans
      ((S.levelOneObjCast_spec hc _ _ (S.levelOneData_eq hc (L.Ψ j))).2.2 a.tgt).symm), hm⟩

/-- The functor on objects: `(λ, q) ↦ (inl λ, q) ∈ X¹`. -/
def lFunObj (x : (S.levelOneConstruction hc).ModelObj L.Ψ) :
    (S.modelEP (S.levelOneModelFamily hc L c₀).Ψ).X.PObj.Level 1 :=
  S.lObjIncl hc L c₀ x.1 (S.lCast hc L x.1 x.2)

/-- The functor on morphisms: `((λ, μ), a) ↦ ((inl λ, inl μ), a) ∈ 𝐗¹`. -/
def lFunMor (φ : (S.levelOneConstruction hc).ModelMor L.Ψ) :
    (S.modelEP (S.levelOneModelFamily hc L c₀).Ψ).X.PMor.Level 1 :=
  S.lMorIncl hc L c₀ φ.1.1 φ.1.2 (S.lTrCast hc L φ.1.1 φ.1.2 φ.2)

theorem modelObjMap_lFunObj (x : (S.levelOneConstruction hc).ModelObj L.Ψ) :
    S.modelObjMap (S.levelOneModelFamily hc L c₀).Ψ
        ((S.modelEP (S.levelOneModelFamily hc L c₀).Ψ).X.PObj.levelVal 1 (S.lFunObj hc L c₀ x)) =
      (show S.regSet 1 from (L.Ψ x.1).1.obj x.2).1 :=
  (S.levelOneObjCast_spec hc _ _ (S.levelOneData_eq hc (L.Ψ x.1))).2.2 x.2

theorem lFunMor_spec (φ : (S.levelOneConstruction hc).ModelMor L.Ψ) :
    (S.modelGroupoid (S.levelOneModelFamily hc L c₀).Ψ).src
        ((S.modelEP (S.levelOneModelFamily hc L c₀).Ψ).X.PMor.levelVal 1 (S.lFunMor hc L c₀ φ)) =
        (S.modelEP (S.levelOneModelFamily hc L c₀).Ψ).X.PObj.levelVal 1
          (S.lFunObj hc L c₀ (((S.levelOneConstruction hc).modelGroupoid L.Ψ).src φ)) ∧
      (S.modelGroupoid (S.levelOneModelFamily hc L c₀).Ψ).tgt
        ((S.modelEP (S.levelOneModelFamily hc L c₀).Ψ).X.PMor.levelVal 1 (S.lFunMor hc L c₀ φ)) =
        (S.modelEP (S.levelOneModelFamily hc L c₀).Ψ).X.PObj.levelVal 1
          (S.lFunObj hc L c₀ (((S.levelOneConstruction hc).modelGroupoid L.Ψ).tgt φ)) ∧
      ((S.modelEP (S.levelOneModelFamily hc L c₀).Ψ).X.PMor.levelVal 1
        (S.lFunMor hc L c₀ φ)).2.mor =
        (show C.toGroupoidStr.morOn (S.regSet 1) from φ.2.mor).1 := by
  obtain ⟨⟨i, j⟩, a⟩ := φ
  obtain ⟨hs, ht, hm⟩ := S.lTrCast_spec hc L i j a
  exact ⟨congrArg (Sigma.mk (β := fun k => ((S.levelOneModelFamily hc L c₀).Ψ k).1.O)
      (Sum.inl i)) hs,
    congrArg (Sigma.mk (β := fun k => ((S.levelOneModelFamily hc L c₀).Ψ k).1.O) (Sum.inl j)) ht,
    hm⟩

/-- **The comparison functor `X_L → X_Ψ¹`** (Corollary 17.1.29): for a covering family `L` of
`F¹` with `L_λ = Ψ_λ¹`, the model `X_L` of `C¹` is the full subcategory of `X_Ψ¹` on the components
`O_λ¹` (`Ψ = (Ψ_λ) ⊔ c₀`), `(λ, q) ↦ (inl λ, q)`, `((λ, μ), a) ↦ ((inl λ, inl μ), a)`. -/
def levelOneModelFunctor :
    EpFunctor ((S.levelOneConstruction hc).modelEP L.Ψ).X
      (S.modelEP (S.levelOneModelFamily hc L c₀).Ψ).X.liftOne where
  obj := S.lFunObj hc L c₀
  mor := S.lFunMor hc L c₀
  src_mor φ := MPolyfold.level_ext (S.lFunMor_spec hc L c₀ φ).1
  tgt_mor φ := MPolyfold.level_ext (S.lFunMor_spec hc L c₀ φ).2.1
  mor_comp φ ψ h := by
    let X := (S.modelEP (S.levelOneModelFamily hc L c₀).Ψ).X
    let Y := ((S.levelOneConstruction hc).modelEP L.Ψ).X
    have hF := fun x y (h : x = y) =>
      congrArg (fun x => X.PObj.levelVal 1 (S.lFunObj hc L c₀ x)) h
    have h' : X.src (X.PMor.levelVal 1 (S.lFunMor hc L c₀ φ)) =
        X.tgt (X.PMor.levelVal 1 (S.lFunMor hc L c₀ ψ)) :=
      (S.lFunMor_spec hc L c₀ φ).1.trans ((hF _ _ h).trans (S.lFunMor_spec hc L c₀ ψ).2.1.symm)
    have hC : C.toGroupoidStr.src (show C.toGroupoidStr.morOn (S.regSet 1) from φ.2.mor).1 =
        C.toGroupoidStr.tgt (show C.toGroupoidStr.morOn (S.regSet 1) from ψ.2.mor).1 := by
      have h1 := congrArg Subtype.val ((S.levelOneConstruction hc).modelFunctor L.Ψ |>.src_mor φ)
      have h2 := congrArg Subtype.val ((S.levelOneConstruction hc).modelFunctor L.Ψ |>.tgt_mor ψ)
      have h3 := congrArg (fun x => (((S.levelOneConstruction hc).modelFunctor L.Ψ).obj x).1) h
      exact h1.trans (h3.trans h2.symm)
    refine MPolyfold.level_ext
      ((?_ : _ = X.comp _ _).trans (EpGroupoid.levelVal_liftComp X h').symm)
    refine S.modelMor_ext ?_ ?_ ?_
    · exact (S.lFunMor_spec hc L c₀ (Y.comp φ ψ)).1.trans ((hF _ _ (Y.src_comp φ ψ h)).trans
        ((S.lFunMor_spec hc L c₀ ψ).1.symm.trans (X.src_comp _ _ h').symm))
    · exact (S.lFunMor_spec hc L c₀ (Y.comp φ ψ)).2.1.trans ((hF _ _ (Y.tgt_comp φ ψ h)).trans
        ((S.lFunMor_spec hc L c₀ φ).2.1.symm.trans (X.tgt_comp _ _ h').symm))
    · refine (S.lFunMor_spec hc L c₀ (Y.comp φ ψ)).2.2.trans ?_
      refine Eq.trans ?_ (modelGroupoid_comp_mor (S := S) (Ψ := (S.levelOneModelFamily hc L c₀).Ψ)
        h').symm
      refine (congrArg Subtype.val (modelGroupoid_comp_mor (S := S.levelOneConstruction hc)
        (Ψ := L.Ψ) h)).trans ((fullSub_comp_val_of _ _ hC).trans ?_)
      rw [(S.lFunMor_spec hc L c₀ φ).2.2, (S.lFunMor_spec hc L c₀ ψ).2.2]
  mor_unit x := by
    let X := (S.modelEP (S.levelOneModelFamily hc L c₀).Ψ).X
    let Y := ((S.levelOneConstruction hc).modelEP L.Ψ).X
    have hF := fun x y (h : x = y) =>
      congrArg (fun x => X.PObj.levelVal 1 (S.lFunObj hc L c₀ x)) h
    refine MPolyfold.level_ext ?_
    refine S.modelMor_ext ?_ ?_ ?_
    · exact (S.lFunMor_spec hc L c₀ (Y.unit x)).1.trans ((hF _ _ (Y.src_unit x)).trans
        (X.src_unit _).symm)
    · exact (S.lFunMor_spec hc L c₀ (Y.unit x)).2.1.trans ((hF _ _ (Y.tgt_unit x)).trans
        (X.tgt_unit _).symm)
    · refine (S.lFunMor_spec hc L c₀ (Y.unit x)).2.2.trans ?_
      change C.toGroupoidStr.unit _ = C.toGroupoidStr.unit _
      rw [S.modelObjMap_lFunObj hc L c₀ x]
      rfl
  isScSmoothMap_obj := by
    refine (MPolyfold.isScSmoothMap_sigma_iff _).2 fun i => ?_
    exact ((S.isLocalScDiffeo_lObjIncl hc L c₀ i).comp
      (S.levelOneObjCast_spec hc _ _ (S.levelOneData_eq hc (L.Ψ i))).2.1).isScSmoothMap
  isScSmoothMap_mor := by
    refine (MPolyfold.isScSmoothMap_sigma_iff _).2 fun p => ?_
    exact ((S.isLocalScDiffeo_lMorIncl hc L c₀ p.1 p.2).comp
      (S.isLocalScDiffeo_lTrCast hc L p.1 p.2)).isScSmoothMap

theorem levelOneModelFunctor_obj (x : (S.levelOneConstruction hc).ModelObj L.Ψ) :
    (S.levelOneModelFunctor hc L c₀).obj x = S.lFunObj hc L c₀ x := rfl

theorem levelOneModelFunctor_mor (φ : (S.levelOneConstruction hc).ModelMor L.Ψ) :
    (S.levelOneModelFunctor hc L c₀).mor φ = S.lFunMor hc L c₀ φ := rfl

theorem levelOneModelFunctor_faithful :
    (S.levelOneModelFunctor hc L c₀).toFunctor.Faithful := by
  refine (GroupoidFunctor.faithful_iff _).2 fun φ φ' hs ht he => ?_
  refine (GroupoidFunctor.faithful_iff _).1 ((S.levelOneConstruction hc).modelFunctor_faithful L.Ψ)
    φ φ' hs ht (Subtype.ext ?_)
  have h := congrArg (fun m => ((S.modelEP (S.levelOneModelFamily hc L c₀).Ψ).X.PMor.levelVal 1
    m).2.mor) he
  exact (S.lFunMor_spec hc L c₀ φ).2.2.symm.trans (h.trans (S.lFunMor_spec hc L c₀ φ').2.2)

theorem levelOneModelFunctor_full :
    (S.levelOneModelFunctor hc L c₀).toFunctor.Full := by
  let X := (S.modelEP (S.levelOneModelFamily hc L c₀).Ψ).X
  refine (GroupoidFunctor.full_iff _).2 fun x x' ψ hs ht => ?_
  have hs' : C.toGroupoidStr.src (X.PMor.levelVal 1 ψ).2.mor =
      (show S.regSet 1 from (L.Ψ x.1).1.obj x.2).1 :=
    (X.PMor.levelVal 1 ψ).2.src_mor.trans
      ((congrArg (S.modelObjMap _) (congrArg (X.PObj.levelVal 1) hs)).trans
        (S.modelObjMap_lFunObj hc L c₀ x))
  have ht' : C.toGroupoidStr.tgt (X.PMor.levelVal 1 ψ).2.mor =
      (show S.regSet 1 from (L.Ψ x'.1).1.obj x'.2).1 :=
    (X.PMor.levelVal 1 ψ).2.tgt_mor.trans
      ((congrArg (S.modelObjMap _) (congrArg (X.PObj.levelVal 1) ht)).trans
        (S.modelObjMap_lFunObj hc L c₀ x'))
  let β : C.toGroupoidStr.morOn (S.regSet 1) :=
    ⟨(X.PMor.levelVal 1 ψ).2.mor, hs' ▸ ((L.Ψ x.1).1.obj x.2).2,
      ht' ▸ ((L.Ψ x'.1).1.obj x'.2).2⟩
  obtain ⟨φ, hφs, hφt, hφ⟩ := (GroupoidFunctor.full_iff _).1
    ((S.levelOneConstruction hc).modelFunctor_full L.Ψ) x x' β (Subtype.ext hs') (Subtype.ext ht')
  refine ⟨φ, hφs, hφt, MPolyfold.level_ext (S.modelMor_ext ?_ ?_ ?_)⟩
  · exact (S.lFunMor_spec hc L c₀ φ).1.trans
      ((congrArg (fun x => X.PObj.levelVal 1 (S.lFunObj hc L c₀ x)) hφs).trans
        (congrArg (X.PObj.levelVal 1) hs).symm)
  · exact (S.lFunMor_spec hc L c₀ φ).2.1.trans
      ((congrArg (fun x => X.PObj.levelVal 1 (S.lFunObj hc L c₀ x)) hφt).trans
        (congrArg (X.PObj.levelVal 1) ht).symm)
  · exact (S.lFunMor_spec hc L c₀ φ).2.2.trans (congrArg Subtype.val hφ)

theorem levelOneModelFunctor_essSurj :
    (S.levelOneModelFunctor hc L c₀).toFunctor.EssSurj := by
  let X := (S.modelEP (S.levelOneModelFamily hc L c₀).Ψ).X
  refine (GroupoidFunctor.essSurj_iff _).2 fun y => ?_
  set w := X.PObj.levelVal 1 y
  have hw : S.modelObjMap _ w ∈ S.regSet 1 :=
    (S.hasRegularity_modelFunctor_obj _ w 1).2 (MPolyfold.levelVal_mem y)
  let β : (S.levelOneGCT hc).Obj := ⟨S.modelObjMap _ w, hw⟩
  obtain ⟨i, hi⟩ := mem_iUnion.1 (L.cover.symm ▸ mem_univ ((S.levelOneGCT hc).toGroupoidStr.π β))
  obtain ⟨q, hq⟩ := (L.Ψ i).1.mem_footprint_iff.1 hi
  obtain ⟨φ₀, hs₀, ht₀⟩ := GroupoidStr.isomorphic_fullSub_iff.1
    (((S.levelOneGCT hc).toGroupoidStr.π_eq_π_iff).1 hq)
  let m : S.ModelMor (S.levelOneModelFamily hc L c₀).Ψ :=
    (S.modelMorEquiv _).symm ⟨X.PObj.levelVal 1 (S.lFunObj hc L c₀ ⟨i, q⟩), φ₀, w,
      hs₀.trans (S.modelObjMap_lFunObj hc L c₀ ⟨i, q⟩).symm, ht₀⟩
  have hm : m ∈ X.PMor.levelSet 1 :=
    (X.isLocalScDiffeo_src.mem_levelSet_iff m 1).1
      (MPolyfold.levelVal_mem (S.lFunObj hc L c₀ ⟨i, q⟩))
  exact ⟨⟨i, q⟩, X.PMor.levelMk 1 m hm, MPolyfold.level_ext rfl, MPolyfold.level_ext rfl⟩

theorem isLocalScDiffeo_levelOneModelFunctor_obj :
    ((S.levelOneConstruction hc).modelEP L.Ψ).X.PObj.IsLocalScDiffeo
      (S.modelEP (S.levelOneModelFamily hc L c₀).Ψ).X.liftOne.PObj
      (S.levelOneModelFunctor hc L c₀).obj :=
  (MPolyfold.isLocalScDiffeo_sigma_iff _).2 fun i =>
    (S.isLocalScDiffeo_lObjIncl hc L c₀ i).comp (S.isLocalScDiffeo_lCast hc L i)

/-- **`X_L → X_Ψ¹` is an equivalence of ep-groupoids** (Definition 10.1.1; Lemma 10.1.2): full,
faithful, essentially surjective (`L` covers `|C¹|`), and a local sc-diffeomorphism on
objects. -/
theorem isEquivalence_levelOneModelFunctor : (S.levelOneModelFunctor hc L c₀).IsEquivalence :=
  EpFunctor.lemma_10_1_2 _
    { faithful := S.levelOneModelFunctor_faithful hc L c₀
      full := S.levelOneModelFunctor_full hc L c₀
      essSurj := S.levelOneModelFunctor_essSurj hc L c₀ }
    (S.isLocalScDiffeo_levelOneModelFunctor_obj hc L c₀)

/-- `X_L → X_Ψ¹` as a morphism of `EP`. -/
abbrev levelOneModelHom :
    (S.levelOneConstruction hc).modelEP L.Ψ ⟶
      (S.modelEP (S.levelOneModelFamily hc L c₀).Ψ).liftOne :=
  S.levelOneModelFunctor hc L c₀

/-- **The model `X_L` of `C¹` and the index raise `X_Ψ¹` are generalized isomorphic.** -/
theorem isGeneralizedIso_levelOneModelHom :
    EPLocalization.EPLoc.IsGeneralizedIso
      (EPLocalization.EPLoc.localizationFunctor.map (S.levelOneModelHom hc L c₀)) :=
  (EPLocalization.EPLoc.isGeneralizedIso_iff_isIso _).2
    (EPLocalization.EPLoc.isInvertedBy_localizationFunctor _
      (S.isEquivalence_levelOneModelFunctor hc L c₀))

/-- **A property invariant under generalized isomorphisms holds for `X_L` iff it holds for the
index raise `X_Ψ¹` of the model of `C`.** -/
theorem levelOneModel_iff {P : EP.{u} → Prop} (hP : IsGenIsoInvariant P) :
    P ((S.levelOneConstruction hc).modelEP L.Ψ) ↔
      P (S.modelEP (S.levelOneModelFamily hc L c₀).Ψ).liftOne :=
  hP (S.isGeneralizedIso_levelOneModelHom hc L c₀)

end ModelLevelOne

/-- **2021 Corollary 17.1.29, p. 766, for every model of `C¹`**: if `C` satisfies (ZHOU), (SLUC)
or (SLR), so does the model `X_L` of `C¹` for every covering family `L` of `F¹` (`X_L` is
generalized isomorphic to the index raise `X_Ψ¹` of a model of `C`, and
`corollary_17_1_29_model`). -/
theorem corollary_17_1_29_of_coveringFamily (hc : S.HasCoveringUniformizers)
    (L : (S.levelOneConstruction hc).CoveringFamily) :
    (S.IsZhou → ((S.levelOneConstruction hc).modelEP L.Ψ).X.IsZhou) ∧
      (S.IsSLUC → ((S.levelOneConstruction hc).modelEP L.Ψ).IsSLUC) ∧
      (S.IsSLR → ((S.levelOneConstruction hc).modelEP L.Ψ).IsSLR) := by
  obtain ⟨h1, h2, h3⟩ := S.corollary_17_1_29_model
    (S.levelOneModelFamily hc L (S.levelOneCover hc))
  exact ⟨fun h => (S.levelOneModel_iff hc L _ isGenIsoInvariant_isZhou).2 (h1 h),
    fun h => (S.levelOneModel_iff hc L _ isGenIsoInvariant_isSLUC).2 (h2 h),
    fun h => (S.levelOneModel_iff hc L _ isGenIsoInvariant_isSLR).2 (h3 h)⟩

/-- **2021 Corollary 17.1.29, p. 766**: if the polyfold `C` satisfies (ZHOU), (SLUC) or (SLR), so
does `C¹` (Definition 17.1.22 for `(C¹, F¹, M_{F¹})`).  "`C¹` satisfies P" asks for a covering
family of `F¹`; we prove it under `F(α) ≠ ∅` for all `α`, which gives one. -/
theorem corollary_17_1_29 (hu : S.HasUniformizers) :
    (S.IsZhou →
        (S.levelOneConstruction (S.hasCoveringUniformizers_of_hasUniformizers hu)).IsZhou) ∧
      (S.IsSLUC →
        (S.levelOneConstruction (S.hasCoveringUniformizers_of_hasUniformizers hu)).IsSLUC) ∧
      (S.IsSLR →
        (S.levelOneConstruction (S.hasCoveringUniformizers_of_hasUniformizers hu)).IsSLR) := by
  obtain ⟨L⟩ := (S.levelOneConstruction _).exists_coveringFamily_iff.2
    ((S.levelOneConstruction _).hasCoveringUniformizers_of_hasUniformizers
      (levelOne_hasUniformizers hu))
  obtain ⟨h1, h2, h3⟩ := S.corollary_17_1_29_of_coveringFamily _ L
  exact ⟨fun h => ⟨L, h1 h⟩, fun h => ⟨L, h2 h⟩, fun h => ⟨L, h3 h⟩⟩

end GCT.PolyfoldConstruction

/-! ### The levels `C^{i+1} := (C^i)¹` -/

/-- **A GCT with a polyfold structure** `(F, M)` in which every object has a uniformizer
(`F(α) ≠ ∅`, implicit in the text); the setting in which `C ↦ C¹` can be iterated. -/
structure GCT.UniformizedPolyfold : Type (u + 1) where
  /-- The GCT `C`. -/
  cat : GCT.{u}
  /-- The polyfold structure `(F, M)`. -/
  str : cat.PolyfoldConstruction
  /-- `F(α) ≠ ∅` for every `α`. -/
  hasUniformizers : str.HasUniformizers

namespace GCT.UniformizedPolyfold

variable (X : GCT.UniformizedPolyfold.{u})

theorem hasCoveringUniformizers : X.str.HasCoveringUniformizers :=
  X.str.hasCoveringUniformizers_of_hasUniformizers X.hasUniformizers

/-- **`C¹`** with the polyfold structure `(F¹, M_{F¹})` (Theorem 17.1.28). -/
def levelOne : GCT.UniformizedPolyfold.{u} where
  cat := X.str.levelOneGCT X.hasCoveringUniformizers
  str := X.str.levelOneConstruction X.hasCoveringUniformizers
  hasUniformizers := GCT.PolyfoldConstruction.levelOne_hasUniformizers X.hasUniformizers

/-- **`C^i`** (2021 p. 766): `C^0 = C`, `C^{i+1} := (C^i)¹`. -/
def level : ℕ → GCT.UniformizedPolyfold.{u}
  | 0 => X
  | i + 1 => (level i).levelOne

@[simp] theorem level_zero : X.level 0 = X := rfl

theorem level_succ (i : ℕ) : X.level (i + 1) = (X.level i).levelOne := rfl

/-- **The inclusion `C^i → C`**: the composite of the inclusions of full subcategories
`C^{i+1} = (C^i)_1 → C^i`. -/
def levelIncl : ∀ i, GroupoidFunctor (X.level i).cat.toGroupoidStr X.cat.toGroupoidStr
  | 0 => GroupoidFunctor.id _
  | i + 1 => (levelIncl i).comp (X.level i).str.levelOneInclusion

theorem levelIncl_succ_obj (i : ℕ) (x : (X.level (i + 1)).cat.Obj) :
    (X.levelIncl (i + 1)).obj x = (X.levelIncl i).obj (show (X.level i).str.regSet 1 from x).1 :=
  rfl

/-- `C^i → C` is injective on objects. -/
theorem injective_levelIncl_obj : ∀ i, Injective (X.levelIncl i).obj
  | 0 => injective_id
  | i + 1 => fun _ _ h => Subtype.ext (injective_levelIncl_obj i h)

/-- `C^i → C` reflects and preserves isomorphisms (it is full). -/
theorem isomorphic_levelIncl_iff : ∀ i (x y : (X.level i).cat.Obj),
    X.cat.toGroupoidStr.Isomorphic ((X.levelIncl i).obj x) ((X.levelIncl i).obj y) ↔
      (X.level i).cat.toGroupoidStr.Isomorphic x y
  | 0, _, _ => Iff.rfl
  | i + 1, x, y => (isomorphic_levelIncl_iff i x.1 y.1).trans
      GroupoidStr.isomorphic_fullSub_iff.symm

/-- **The regularity of `C^i` is that of `C` shifted by `i`**: `x` has regularity `m` in `C^i`
iff its image has regularity `m + i` in `C`. -/
theorem hasRegularity_level_iff : ∀ i (x : (X.level i).cat.Obj) (m : ℕ),
    (X.level i).str.HasRegularity m x ↔ X.str.HasRegularity (m + i) ((X.levelIncl i).obj x)
  | 0, _, _ => Iff.rfl
  | i + 1, x, m => by
    rw [show (X.level (i + 1)).str.HasRegularity m x ↔ (X.level i).str.HasRegularity (m + 1) x.1
      from GCT.PolyfoldConstruction.levelOne_hasRegularity_iff_of_hasUniformizers
        (X.level i).hasUniformizers x m, hasRegularity_level_iff i x.1 (m + 1),
      show m + 1 + i = m + (i + 1) by omega]
    rfl

/-- **The objects of `C^i` are those of `C_i`**: the image of `C^i → C` is `C_i`. -/
theorem range_levelIncl_obj : ∀ i, range (X.levelIncl i).obj = X.str.regSet i
  | 0 => by
    rw [X.str.regSet_zero X.hasCoveringUniformizers]
    exact range_id
  | i + 1 => by
    ext β
    constructor
    · rintro ⟨x, rfl⟩
      have := (X.hasRegularity_level_iff i x.1 1).1 x.2
      rwa [show 1 + i = i + 1 by omega] at this
    · intro hβ
      obtain ⟨x, rfl⟩ : β ∈ range (X.levelIncl i).obj := by
        rw [range_levelIncl_obj i]
        exact X.str.regSet_antitone (Nat.le_succ i) hβ
      refine ⟨⟨x, (X.hasRegularity_level_iff i x 1).2 ?_⟩, rfl⟩
      rwa [show 1 + i = i + 1 by omega]

theorem levelIncl_obj_mem (i : ℕ) (x : (X.level i).cat.Obj) :
    (X.levelIncl i).obj x ∈ X.str.regSet i :=
  X.range_levelIncl_obj i ▸ mem_range_self x

/-- **`C^i → C_i`**: the inclusion corestricted to the full subcategory `C_i`. -/
def levelEquivSub (i : ℕ) :
    GroupoidFunctor (X.level i).cat.toGroupoidStr (X.str.regSub i) :=
  (X.levelIncl i).corestrict _ (X.levelIncl_obj_mem i)

/-- **`|C^i| → |C_i|` is a bijection.** -/
theorem bijective_orbitMap_levelEquivSub (i : ℕ) :
    Bijective (X.levelEquivSub i).orbitMap := by
  refine ⟨fun a b h => ?_, fun z => ?_⟩
  · induction a using Quotient.inductionOn with | h x => ?_
    induction b using Quotient.inductionOn with | h y => ?_
    have h' := GroupoidStr.isomorphic_fullSub_iff.1 (((X.str.regSub i).π_eq_π_iff).1 h)
    exact ((X.level i).cat.toGroupoidStr.π_eq_π_iff).2 ((X.isomorphic_levelIncl_iff i x y).1 h')
  · induction z using Quotient.inductionOn with | h β => ?_
    obtain ⟨x, hx⟩ : β.1 ∈ range (X.levelIncl i).obj := (X.range_levelIncl_obj i).symm ▸ β.2
    exact ⟨(X.level i).cat.toGroupoidStr.π x, congrArg (X.str.regSub i).π (Subtype.ext hx)⟩

/-- `|C^i| ≃ |C_i|`. -/
def levelOrbitEquiv (i : ℕ) :
    (X.level i).cat.toGroupoidStr.OrbitSpace ≃ (X.str.regSub i).OrbitSpace :=
  Equiv.ofBijective _ (X.bijective_orbitMap_levelEquivSub i)

/-- **The natural topology of `|C_i|`** (2021 p. 766), transported from the GCT `C^i`. -/
@[instance_reducible]
def levelTopology (i : ℕ) : TopologicalSpace (X.str.regSub i).OrbitSpace :=
  TopologicalSpace.coinduced (X.levelOrbitEquiv i) (X.level i).cat.top

/-- `|C^i| ≃ₜ |C_i|`. -/
def levelOrbitHomeomorph (i : ℕ) :
    @Homeomorph (X.level i).cat.toGroupoidStr.OrbitSpace (X.str.regSub i).OrbitSpace
      (X.level i).cat.top (X.levelTopology i) :=
  @Equiv.toHomeomorph _ _ (X.level i).cat.top (X.levelTopology i) (X.levelOrbitEquiv i)
    fun _ => isOpen_coinduced.symm

/-- **`|C_i|` is metrizable for every `i`** (2021 p. 766). -/
theorem metrizableSpace_level (i : ℕ) :
    @MetrizableSpace (X.str.regSub i).OrbitSpace (X.levelTopology i) := by
  let _ := X.levelTopology i
  let _ := (X.level i).cat.top
  have := (X.level i).cat.metrizable
  exact (X.levelOrbitHomeomorph i).symm.isEmbedding.metrizableSpace

/-- For `i = 1` the topology is that of Theorem 17.1.28 (`levelOneTopology`). -/
theorem levelTopology_one :
    X.levelTopology 1 = X.str.levelOneTopology X.hasCoveringUniformizers := by
  have h : ⇑(X.levelOrbitEquiv 1) = id := by
    funext z
    induction z using Quotient.inductionOn with | h x => rfl
  rw [levelTopology, h]
  exact coinduced_id

/-- **2021 p. 766, `C^{i+1} := (C^i)¹`**: `C^i` is a GCT with a polyfold structure, `C^{i+1}` is
`(C^i)¹` with the polyfold structure of Theorem 17.1.28, `C^i → C` identifies the objects of `C^i`
with `C_i` (regularity shifted by `i`) and `|C^i|` with `|C_i|`, which is metrizable. -/
theorem level_spec (i : ℕ) :
    X.level (i + 1) = (X.level i).levelOne ∧
      (∀ (x : (X.level i).cat.Obj) (m : ℕ),
        (X.level i).str.HasRegularity m x ↔ X.str.HasRegularity (m + i) ((X.levelIncl i).obj x)) ∧
      Injective (X.levelIncl i).obj ∧ range (X.levelIncl i).obj = X.str.regSet i ∧
      Bijective (X.levelEquivSub i).orbitMap ∧
      @MetrizableSpace (X.str.regSub i).OrbitSpace (X.levelTopology i) :=
  ⟨rfl, X.hasRegularity_level_iff i, X.injective_levelIncl_obj i, X.range_levelIncl_obj i,
    X.bijective_orbitMap_levelEquivSub i, X.metrizableSpace_level i⟩

/-- **Corollary 17.1.29 for all levels**: if `C` satisfies (ZHOU), (SLUC) or (SLR), so does every
`C^i`. -/
theorem level_properties (i : ℕ) :
    (X.str.IsZhou → (X.level i).str.IsZhou) ∧ (X.str.IsSLUC → (X.level i).str.IsSLUC) ∧
      (X.str.IsSLR → (X.level i).str.IsSLR) := by
  induction i with
  | zero => exact ⟨id, id, id⟩
  | succ i ih =>
    obtain ⟨h1, h2, h3⟩ := (X.level i).str.corollary_17_1_29 (X.level i).hasUniformizers
    exact ⟨fun h => h1 (ih.1 h), fun h => h2 (ih.2.1 h), fun h => h3 (ih.2.2 h)⟩

end GCT.UniformizedPolyfold

end Polyfold
