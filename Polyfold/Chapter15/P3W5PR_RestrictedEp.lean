import Polyfold.Chapter15.P3W5PR_TameBranched
import Polyfold.Chapter11.BranchedEquivalence
import Polyfold.Chapter7.NaturalAction
import Polyfold.Chapter7.Michael
import Polyfold.Chapter7.ProperSubsets

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 15,
§15.2, **Remark 15.2.3** (p. 689; 2017: Remark 15.2) and the last sentence of **Theorem 15.2.5**
(p. 690): the functor `z ↦ Λ(f(z))` **on the ep-groupoid `U(x)`**.

# `Λ ∘ f` as a tame branched ep⁺-subgroupoid of the ep-groupoid `U(x)`

## The text, paraphrased

(Remark 15.2.3) Considering the ep-groupoid `U(x)`, the functor `U(x) → ℚ⁺`, `z ↦ Λ(f(z))`, is a
branched ep⁺-subgroupoid, tame, with support `M_{U(x)}`.  (Theorem 15.2.5) In the boundary case
`Λ ∘ f` is a tame branched ep⁺-subgroupoid on `U(x)`.

## What is formalized

The ep-groupoid `U(x)` is read as the translation ep-groupoid `G_x ⋉ U(x)`
(`NaturalRep.translationEpGroupoid`, Chapter 7): by Theorem 7.1.13 (3) the functor
`Γ : G_x ⋉ U(x) → X` is fully faithful onto the full subcategory on `U(x)` (`NaturalRep.functor`,
`full`, `faithful`), and Proposition 7.1.19 identifies the orbit spaces.  `Θ_U(y) = Θ(y)` is the
functor `Θ` restricted to `U(x)`.

* `locallyFinite_image_of_isClosedMap`: a closed map with finite fibres carries locally finite
  families to locally finite families.
* `NaturalRep.isClosedMap_translation_π`, `NaturalRep.finite_fiber_translation_π`: the orbit map
  of `G_x ⋉ U(x)` is closed with finite fibres (`G_x` finite).
* `NaturalRep.paracompactSpace_orbitSupp_translation`: for `supp(Θ_U)` closed in `U(x)`, the
  orbit space `|supp(Θ_U)|` is paracompact (Definition 9.1.2 (1), new in 2021), by Michael's
  criterion (Lemma 2.7.3, `paracompactSpace_of_closed_refinement`).
* `NaturalRep.nonempty_tameBranching_translation`: a tame local branching structure of `Θ` at a
  point of `U(x)` (Definition 9.3.6) gives one of `Θ_U` on `G_x ⋉ U(x)` (restricted to a natural
  representation of `G_x ⋉ U(x)` and moved by the sc-diffeomorphism `U(x) → U(x)` of the
  inclusion).
* **`NaturalRep.isTameBranched_translation`**: if `Θ ≥ 0` is a functor, `supp Θ` is closed, and
  every point of `supp Θ ∩ U(x)` is smooth with a tame local branching structure, then `Θ_U` is a
  branched ep⁺-subgroupoid of `G_x ⋉ U(x)` (Definition 9.1.2) and tame (Definition 9.3.6).
* **`remark_15_2_3_restricted_hyp`** (Remark 15.2.3) and **`theorem_15_2_5_restricted_hyp`**
  (Theorem 15.2.5): at an interior point of transversality, resp. a point of good position, there
  is `U(x)` with the natural `G_x`-action on which `z ↦ Λ(f(z))` is a tame branched
  ep⁺-subgroupoid of `G_x ⋉ U(x)`.

## Reading

* "The ep-groupoid `U(x)`" is the translation groupoid `G_x ⋉ U(x)`, the form in which Chapter 7
  proves that it is an ep-groupoid; the full subcategory of `X` on `U(x)` is isomorphic to it.
* The inherited hypothesis `IsScFredholmSectionTame` (Part I's Theorem 3.6.8) is as in §15.2.
  No paracompactness hypothesis is needed on `U(x)`: it is proved.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

/-! ### Closed maps with finite fibres -/

/-- **A closed map with finite fibres carries a locally finite family to a locally finite
family.** -/
theorem locallyFinite_image_of_isClosedMap {ι : Type*} {Z Y : Type*} [TopologicalSpace Z]
    [TopologicalSpace Y] {p : Z → Y} (hp : IsClosedMap p) (hfin : ∀ y, (p ⁻¹' {y}).Finite)
    {v : ι → Set Z} (hv : LocallyFinite v) : LocallyFinite fun i => p '' v i := by
  intro y
  have hN : ∀ z : Z, ∃ N ∈ 𝓝 z, {i | (v i ∩ N).Nonempty}.Finite := fun z => hv z
  choose N hN hNf using hN
  set W : Set Z := ⋃ z ∈ p ⁻¹' {y}, interior (N z) with hW
  have hWo : IsOpen W := isOpen_biUnion fun _ _ => isOpen_interior
  have hfib : p ⁻¹' {y} ⊆ W := fun z hz =>
    mem_biUnion hz (mem_interior_iff_mem_nhds.2 (hN z))
  have hy : y ∉ p '' Wᶜ := by
    rintro ⟨z, hz, hzy⟩
    exact hz (hfib hzy)
  refine ⟨(p '' Wᶜ)ᶜ, (hp _ hWo.isClosed_compl).isOpen_compl.mem_nhds hy, ?_⟩
  refine ((hfin y).biUnion fun z _ => hNf z).subset ?_
  rintro i ⟨_, ⟨z, hzv, rfl⟩, hzV⟩
  have hzW : z ∈ W := by
    by_contra h
    exact hzV ⟨z, h, rfl⟩
  obtain ⟨z', hz', hzN⟩ := mem_iUnion₂.1 hzW
  exact mem_iUnion₂.2 ⟨z', hz', z, hzv, interior_subset hzN⟩

namespace EpGroupoid

namespace NaturalRep

open scoped Polyfold.EpGroupoid.NaturalRep

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {x : Obj} (R : X.NaturalRep x)

/-! ### The orbit map of `G_x ⋉ U(x)` -/

/-- Two points of `U(x)` have the same orbit in `G_x ⋉ U(x)` iff they differ by the action. -/
theorem translation_π_eq_π_iff {y z : R.U} :
    R.translationEpGroupoid.π y = R.translationEpGroupoid.π z ↔ ∃ g : X.Isotropy x, g • y = z :=
  ⟨fun h => by
    obtain ⟨φ, hs, ht⟩ := (R.translationEpGroupoid.π_eq_π_iff).1 h
    exact ⟨φ.1, by rw [← hs]; exact ht⟩,
   fun ⟨g, hg⟩ => (R.translationEpGroupoid.π_eq_π_iff).2 ⟨(g, y), rfl, hg⟩⟩

/-- Every closed subset of `U(x)` is proper in `G_x ⋉ U(x)` (Definition 7.5.8). -/
theorem translation_isProperSubset {C : Set R.U} (hC : IsClosed C) :
    R.translationEpGroupoid.IsProperSubset C := by
  have h := R.translation_isProperMap C
  rw [hC.closure_eq] at h
  exact h

/-- Every open subset of `U(x)` has the properness property in `G_x ⋉ U(x)`. -/
theorem translation_hasPropernessProperty {V : Set R.U} (hV : IsOpen V) :
    R.translationEpGroupoid.HasPropernessProperty V :=
  ⟨hV, R.translation_isProperSubset isClosed_closure⟩

/-- The orbit map of `G_x ⋉ U(x)` is closed (Proposition 7.5.10 (1)). -/
theorem isClosedMap_translation_π : IsClosedMap R.translationEpGroupoid.π := fun _ hC =>
  R.translationEpGroupoid.proposition_7_5_10_one (R.translation_isProperSubset hC)

/-- The fibres of the orbit map of `G_x ⋉ U(x)` are finite (`G_x` is finite). -/
theorem finite_fiber_translation_π (o : R.translationEpGroupoid.OrbitSpace) :
    (R.translationEpGroupoid.π ⁻¹' {o}).Finite := by
  have := NatRepConstruction.finite_isotropy X x
  by_cases h : ∃ y, R.translationEpGroupoid.π y = o
  · obtain ⟨y, rfl⟩ := h
    refine (finite_range fun g : X.Isotropy x => g • y).subset fun z hz => ?_
    obtain ⟨g, hg⟩ := (R.translation_π_eq_π_iff).1 (hz : _ = _).symm
    exact ⟨g, hg⟩
  · simp only [not_exists] at h
    convert finite_empty
    ext z
    exact ⟨fun hz => h z hz, fun hz => hz.elim⟩

/-! ### Paracompactness of `|supp(Θ_U)|` -/

/-- **`|supp(Θ_U)|` is paracompact** for `G_x ⋉ U(x)` when `supp(Θ_U)` is closed in `U(x)`
(Definition 9.1.2 (1)): the orbit map restricted to `supp(Θ_U)` is closed with finite fibres, so
it carries a locally finite closed refinement of the pulled-back cover to one of the cover
(Michael's criterion, `paracompactSpace_of_closed_refinement`). -/
theorem paracompactSpace_orbitSupp_translation {Θ : R.U → ℚ} (hcl : IsClosed (supp Θ)) :
    ParacompactSpace (R.translationEpGroupoid.orbitSupp Θ) := by
  set T := R.translationEpGroupoid
  set S : Set R.U := supp Θ
  have : ParacompactSpace S := hcl.isClosedEmbedding_subtypeVal.paracompactSpace
  let p : S → T.orbitSupp Θ := fun s => ⟨T.π s, mem_image_of_mem _ s.2⟩
  have hpc : Continuous p := (T.continuous_π.comp continuous_subtype_val).subtype_mk _
  have hps : Surjective p := by
    rintro ⟨_, s, hs, rfl⟩
    exact ⟨⟨s, hs⟩, rfl⟩
  have hpcl : IsClosedMap p := by
    intro C hC
    have hC' : IsClosed ((↑) '' C : Set R.U) := hcl.isClosedEmbedding_subtypeVal.isClosedMap C hC
    have e : p '' C = (↑) ⁻¹' (T.π '' ((↑) '' C)) := by
      ext o
      constructor
      · rintro ⟨s, hs, rfl⟩
        exact ⟨s, ⟨s, hs, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨s, hs, rfl⟩, ho⟩
        exact ⟨s, hs, Subtype.ext ho⟩
    rw [e]
    exact (R.isClosedMap_translation_π _ hC').preimage continuous_subtype_val
  have hpfin : ∀ o, (p ⁻¹' {o}).Finite := fun o => by
    have hf := R.finite_fiber_translation_π o.1
    refine (hf.preimage (Subtype.val_injective.injOn)).subset fun s hs => ?_
    exact congrArg Subtype.val (show p s = o from hs)
  refine paracompactSpace_of_closed_refinement fun α s hso hsu => ?_
  obtain ⟨v, hvc, hvu, hvf, hvs⟩ := exists_closed_precise_refinement (fun a => p ⁻¹' s a)
    (fun a => (hso a).preimage hpc) (by rw [← preimage_iUnion, hsu, preimage_univ])
  refine ⟨α, fun a => p '' v a, fun a => hpcl _ (hvc a), ?_,
    locallyFinite_image_of_isClosedMap hpcl hpfin hvf, fun a => ⟨a, image_subset_iff.2 (hvs a)⟩⟩
  rw [← image_iUnion, hvu, image_univ, hps.range_eq]

/-! ### Moving tame local branching structures to `G_x ⋉ U(x)` -/

/-- **A tame local branching structure of `Θ` at `y ∈ U(x)` gives one of `Θ_U = Θ|U(x)` on
`G_x ⋉ U(x)`** (Definition 9.3.6): restrict to the image of a natural representation of
`G_x ⋉ U(x)` at `y` inside `U(y)`, and move by the sc-diffeomorphism `X ⊇ U(x) → U(x)`. -/
theorem nonempty_tameBranching_translation {Θ : Obj → ℚ} {y : R.U}
    (C : X.TameBranchingStructure Θ y) :
    Nonempty (R.translationEpGroupoid.TameBranchingStructure (fun z : R.U => Θ z) y) := by
  set T := R.translationEpGroupoid
  have hf : X.PObj.IsScDiffeoOn T.PObj (MPolyfold.openRetraction R.U) Subtype.val R.U univ :=
    (MPolyfold.isScDiffeoOn_subtypeVal (P := X.PObj) R.isOpen_U).symm
  obtain ⟨R', hR'⟩ := T.theorem_7_1_13 y (C.isOpen_U.preimage continuous_subtype_val) C.mem_U
  have hVo : IsOpen (Subtype.val '' R'.U : Set Obj) :=
    R.isOpen_U.isOpenMap_subtype_val _ R'.isOpen_U
  have hyV : (y : Obj) ∈ Subtype.val '' R'.U := ⟨y, R'.mem_U, rfl⟩
  have hVC : Subtype.val '' R'.U ⊆ C.U := image_subset_iff.2 hR'
  have hVR : Subtype.val '' R'.U ⊆ R.U := Subtype.coe_image_subset _ _
  let B := C.toLocalBranchingStructure.restrict hVo hyV hVC
  have hxy : MPolyfold.openRetraction R.U (y : Obj) = y := MPolyfold.openRetraction_of_mem y.2
  have hΘ : ∀ u ∈ R.U, (fun z : R.U => Θ z) (MPolyfold.openRetraction R.U u) = Θ u :=
    fun u hu => by simp only [MPolyfold.openRetraction_of_mem hu]
  let B' := B.mapDiffeo (Θ' := fun z : R.U => Θ z) hf y.2 hxy hΘ
  have hU : B'.U = R'.U := by
    ext z
    change z ∈ univ ∩ Subtype.val ⁻¹' ((Subtype.val '' R'.U) ∩ R.U) ↔ _
    simp only [univ_inter, mem_preimage, Subtype.val_injective.mem_set_image,
      inter_eq_left.2 hVR]
  have hT : ∀ i, X.PObj.HasTameInducedStructure (B.M i) := fun i =>
    MPolyfold.HasTameInducedStructure.inter_isOpen (C.isSmoothSubmanifold i)
      (C.hasTameInducedStructure i) hVo
  exact ⟨{ toLocalBranchingStructure := B'
           rep := R'
           U_eq := hU
           hasPropernessProperty := by
             rw [show B'.U = R'.U from hU]
             exact R.translation_hasPropernessProperty R'.isOpen_U
           hasTameInducedStructure := fun i =>
             MPolyfold.HasTameInducedStructure.image_of_isScDiffeoOn
               ((B.isSmoothSubmanifold i).inter_isOpen hf.isScSmoothOn.isOpen)
               (MPolyfold.HasTameInducedStructure.inter_isOpen (B.isSmoothSubmanifold i)
                 (hT i) hf.isScSmoothOn.isOpen) hf inter_subset_right }⟩

/-! ### `Θ_U` is a tame branched ep⁺-subgroupoid of `G_x ⋉ U(x)` -/

/-- **`Θ` restricted to `U(x)` is a tame branched ep⁺-subgroupoid of `G_x ⋉ U(x)`**
(Definitions 9.1.2 and 9.3.6): if `Θ ≥ 0` is a functor on `X` with closed support, and every
point of `supp Θ ∩ U(x)` is smooth with a tame local branching structure of `Θ`. -/
theorem isTameBranched_translation {Θ : Obj → ℚ} (hnn : ∀ y, 0 ≤ Θ y) (hfun : X.IsFunctorial Θ)
    (hcl : IsClosed (supp Θ)) (hsm : ∀ y ∈ R.U, 0 < Θ y → y ∈ X.PObj.smoothSet)
    (ht : ∀ y ∈ R.U, 0 < Θ y → Nonempty (X.TameBranchingStructure Θ y)) :
    R.translationEpGroupoid.IsBranchedEpSubgroupoid (fun z : R.U => Θ z) ∧
      R.translationEpGroupoid.IsTameBranched (fun z : R.U => Θ z) := by
  have htame : ∀ z ∈ supp (fun z : R.U => Θ z),
      Nonempty (R.translationEpGroupoid.TameBranchingStructure (fun z : R.U => Θ z) z) :=
    fun z hz => by
      obtain ⟨C⟩ := ht z z.2 hz
      exact R.nonempty_tameBranching_translation C
  have hfun' : R.translationEpGroupoid.IsFunctorial (fun z : R.U => Θ z) := fun φ => by
    have h := hfun (R.Γ φ.1 φ.2)
    rw [R.src_Γ φ.1 φ.2 φ.2.2, R.tgt_Γ φ.1 φ.2 φ.2.2] at h
    exact h
  have hB : R.translationEpGroupoid.IsBranchedEpSubgroupoid (fun z : R.U => Θ z) :=
    { nonneg := fun z => hnn z
      isFunctorial := hfun'
      support_subset := fun z hz =>
        (MPolyfold.mem_smoothSet_restrictOpen_iff R.isOpen_U z).2 (hsm z z.2 hz)
      paracompactSpace_orbitSupp :=
        R.paracompactSpace_orbitSupp_translation (hcl.preimage continuous_subtype_val)
      localBranching := fun z hz =>
        (htame z hz).map TameBranchingStructure.toLocalBranchingStructure }
  exact ⟨hB, htame⟩

end NaturalRep

end EpGroupoid

/-! ### Remark 15.2.3 and Theorem 15.2.5 on the ep-groupoid `U(x)` -/

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid
open scoped Polyfold.EpGroupoid.NaturalRep

variable {A : SEP.{u}}

/-- **Remark 15.2.3 (2017: Remark 15.2), p. 689, on the ep-groupoid `U(x)`**, with the inherited
tame-germ hypothesis `hft`: at a point `x` with `d_X(x) = 0` where `(f, Λ)` is transversal, there
is a neighbourhood `U(x)` with the natural `G_x`-action, `d_X ≡ 0` on it, such that
`z ↦ Λ(f(z))` is a branched ep⁺-subgroupoid (Definition 9.1.2) of the ep-groupoid
`U(x) = G_x ⋉ U(x)`, tame (Definition 9.3.6). -/
theorem remark_15_2_3_restricted_hyp {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ)
    {x : A.Obj} (hd : A.X.PObj.degIndex x = 0) (htr : IsTransversalAt f Λ x) :
    ∃ R : A.X.NaturalRep x, (∀ y ∈ R.U, A.X.PObj.degIndex y = 0) ∧
      R.translationEpGroupoid.IsBranchedEpSubgroupoid (fun z : R.U => (Λ (f z) : ℚ)) ∧
      R.translationEpGroupoid.IsTameBranched (fun z : R.U => (Λ (f z) : ℚ)) := by
  obtain ⟨R, _, _, _, _, _, _, _, _, _, _, hd', hon, _⟩ := theorem_15_2_2_hyp hf hft hΛ hd htr
  have hfc : Continuous f := continuousOn_univ.1 hft.isScSmooth.2.continuousOn
  refine ⟨R, hd', R.isTameBranched_translation (Θ := fun z => (Λ (f z) : ℚ))
    (fun z => NNRat.coe_nonneg (Λ (f z))) (isFunctorial_comp hf hΛ) ?_
    (fun y _ hy => mem_smoothSet_of_pos hft hΛ (by exact_mod_cast hy))
    (fun y hyU hy => ?_)⟩
  · have h := isClosed_supp_comp hf.1.1.1 hfc hΛ
    convert h using 1
    ext y
    change (0 : ℚ) < (Λ (f y) : ℚ) ↔ 0 < Λ (f y)
    exact_mod_cast Iff.rfl
  · have hpos : 0 < Λ (f y) := by exact_mod_cast hy
    exact remark_15_2_3_tame_hyp hf hft hΛ (hd' y hyU) ⟨hpos, hon y hyU hpos⟩

/-- **Theorem 15.2.5 (2017: Theorem 15.3), p. 690, last sentence, on the ep-groupoid `U(x)`**,
with the inherited tame-germ hypothesis `hft`: at a point of good position (Definition 15.2.4)
there is a neighbourhood `U(x)` with the natural `G_x`-action on which `z ↦ Λ(f(z))` is a tame
branched ep⁺-subgroupoid of the ep-groupoid `U(x) = G_x ⋉ U(x)` (Definitions 9.1.2, 9.3.6). -/
theorem theorem_15_2_5_restricted_hyp {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ)
    {x : A.Obj} (hgp : IsGoodPositionAt f Λ x) :
    ∃ R : A.X.NaturalRep x,
      R.translationEpGroupoid.IsBranchedEpSubgroupoid (fun z : R.U => (Λ (f z) : ℚ)) ∧
      R.translationEpGroupoid.IsTameBranched (fun z : R.U => (Λ (f z) : ℚ)) := by
  obtain ⟨R, _, _, _, _, _, _, _, _, _, _, _, _, _, hgpU, _⟩ := theorem_15_2_5_hyp hf hft hΛ hgp
  have hfc : Continuous f := continuousOn_univ.1 hft.isScSmooth.2.continuousOn
  refine ⟨R, R.isTameBranched_translation (Θ := fun z => (Λ (f z) : ℚ))
    (fun z => NNRat.coe_nonneg (Λ (f z))) (isFunctorial_comp hf hΛ) ?_
    (fun y _ hy => mem_smoothSet_of_pos hft hΛ (by exact_mod_cast hy))
    (fun y hyU hy => theorem_15_2_5_tame_hyp hf hft (hgpU y hyU (by exact_mod_cast hy)))⟩
  have h := isClosed_supp_comp hf.1.1.1 hfc hΛ
  convert h using 1
  ext y
  change (0 : ℚ) < (Λ (f y) : ℚ) ↔ 0 < Λ (f y)
  exact_mod_cast Iff.rfl

end SBLocalization

end Polyfold
