import Polyfold.Chapter17.ModelExamples

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.3 (pp. 784–785): **Definition 17.3.1** (subpolyfold), **Definition 17.3.2** (the alternative
definition through a model `X_Ψ`), **Remark 17.3.3** and **Proposition 17.3.4**.  Numbers and pages
are the 2021 text's.

# Subpolyfolds of a GCT with a polyfold structure

## The text, paraphrased

(Definition 17.3.1, p. 784) Let the GCT `C` carry the polyfold structure `(F, M)`.  A subpolyfold
`A` of `C` is a saturated full subcategory such that for an object `α` of `A` and `Ψ ∈ F(α)`,
`Ψ : G ⋉ O → C`, the set `A_Ψ ⊆ O` of all objects with `Ψ(A_Ψ) ⊆ A` is a sub-M-polyfold of `O`.
It only has to be checked for a covering family.  (Definition 17.3.2) A saturated full subcategory
`A` is a subpolyfold provided for a suitable sc-smooth model `X_Ψ` with natural equivalence
`Γ_Ψ : X_Ψ → C` the preimage of `A` under `Γ_Ψ` is an ep-subgroupoid (Definition 7.1.21).
(Remark 17.3.3) The choice of `X_Ψ` does not matter.  (Proposition 17.3.4, pp. 784–785) The two
definitions are equivalent.  *Proof.* (17.3.1 ⇒ 17.3.2) For `a` in the preimage, in the domain
`O` of some `Ψ` of the covering family, `A ∩ O` is a sub-M-polyfold.  (17.3.2 ⇒ 17.3.1) For a
uniformizer `Ψ'` and `a' ∈ A_Ψ'` there are `x' ∈ X_Ψ` and `φ' : Ψ'(a') → Γ(x')`, so
`(a', φ', x') ∈ M(Ψ', Ψ)`; with an admissible triple `U(a') ←s U(a', φ', x') →t U(x')`,
`σ = t ∘ (s|U(a'))⁻¹` and saturation give `Ψ'(a) ∈ A ⟺ Ψ(σ(a)) ∈ A`, so `σ⁻¹` maps
`A_Ψ ∩ U(x')` onto `A_Ψ' ∩ U(a')`, a sub-M-polyfold.

## What is formalized (namespace `Polyfold.GCT.PolyfoldConstruction`)

* Sub-M-polyfolds (namespace `Polyfold.MPolyfold`): `isSubMPolyfold_of_forall_isScDiffeoOn` (a set
  which near each point is the preimage of a sub-M-polyfold under an sc-diffeomorphism of open
  sets), `IsLocalScDiffeo.isSubMPolyfold_preimage`, `isSubMPolyfold_sigma_iff` (a subset of a
  disjoint union), `isSubMPolyfold_singleton`, `not_isSubMPolyfold_of_dense` (a dense set with
  dense complement is not one).
* **Definition 17.3.1**: `IsSubpolyfold`; **Definition 17.3.2**: `IsSubpolyfoldModel`.
* The model: `isSaturated_preimage_modelFunctor`, `isSubMPolyfold_preimage_modelFunctor_iff`
  (the preimage in `X_Ψ` is a sub-M-polyfold iff every `A_{Ψ_λ}` is one),
  `isEpSubgroupoid_preimage_modelFunctor_iff`.
* The transfer of the proof of 17.3.4: `isSubMPolyfold_of_forall_tr` (if every `a' ∈ A_Ψ'` is the
  source of some `(a', φ, x) ∈ M(Ψ', Ψ)` with `A_Ψ` a sub-M-polyfold, then `A_Ψ'` is one),
  `isSubMPolyfold_of_isCoveringFamily` (a covering family transfers to every uniformizer),
  `IsSubpolyfold.isSubMPolyfold` (17.3.1 transfers to every uniformizer when `F(α) ≠ ∅` on `A`).
* **Remark 17.3.3**: `remark_17_3_3` (the preimage is an ep-subgroupoid in every model once it is
  in one), `isSubpolyfoldModel_iff_forall`.
* **Proposition 17.3.4**: `isSubpolyfold_of_isSubpolyfoldModel` (17.3.2 ⇒ 17.3.1, no hypothesis),
  `proposition_17_3_4_of_nonempty`, `proposition_17_3_4` (under `F(α) ≠ ∅`), and
  `isSubpolyfold_iff_forall_unif` (both are equivalent to: `A_Ψ` is a sub-M-polyfold for every
  uniformizer `Ψ` of `F`).
* `PolyfoldConstruction.restrictF`: the polyfold structure `(F', M)` for smaller sets
  `F'(α) ⊆ F(α)`.
* **`proposition_17_3_4_empty_family`**: why the standing reading `F(α) ≠ ∅` is needed: with
  some `F(α)` empty, the direction 17.3.1 ⇒ 17.3.2 does not hold as we read it.
* Witnesses: `reflection_isSubpolyfold_zero` (`A = {0}` in `ℤ/2 ⋉ ℝ`, with isotropy `ℤ/2`),
  `overlap_isSubpolyfold_zero` (the same `A` for the construction with three overlapping
  uniformizers, the transfer reaching `Ψ₁ : ℤ/2 ⋉ (−2, 2)` and `Ψ₂ : {1} ⋉ (1, 3)`), and
  `reflection_not_isSubpolyfold_rat` (the saturated set `{x | x ∈ ℚ}` is not a subpolyfold).

## Readings

* "Saturated full subcategory" is read as a saturated set `A` of objects (`GroupoidStr.IsSaturated`,
  `π⁻¹(π(A)) = A`); the full subcategory on it is `GroupoidStr.fullSub A`, built in
  `SubpolyfoldStructure.lean`.
* "The set of all objects `A_Ψ ⊆ O` satisfying `Ψ(A_Ψ) ⊆ A`" is read as the largest such set,
  `A_Ψ = Ψ⁻¹(A)`.
* "A suitable sc-smooth model `X_Ψ`" is the model of a covering family (p. 752), so Definition
  17.3.2 includes the existence of a covering family.
* The direction 17.3.1 ⇒ 17.3.2 uses, at `a ∈ O` with `Ψ(a) ∈ A`, a uniformizer `Ψ' ∈ F(Ψ(a))`;
  Definition 17.3.1 only constrains `Ψ ∈ F(α)` for `α ∈ A`, and `Ψ` itself need not lie in any
  `F(α)` with `α ∈ A`.  So we read `F(α) ≠ ∅`, the standing reading of §17.1 (`HasUniformizers`,
  as in the choice of covering families on p. 752).  The proof is the text's local argument of the
  other direction, applied to `(a, 1, q') ∈ M(Ψ, Ψ')`, `Ψ'(q') = Ψ(a)`.  The example
  `proposition_17_3_4_empty_family` shows why the reading is needed: with footprints covering
  `|C|` but `F(α) = ∅` exactly on a dense saturated `A` with dense complement, the direction
  does not hold as we read it.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u v

/-! ### Sub-M-polyfolds: local criteria, preimages, disjoint unions -/

namespace MPolyfold

section Criteria

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}

/-- **The local step of the criterion below**: if near `x ∈ A` there are an sc-diffeomorphism
`f : W → V` of open sets and a sub-M-polyfold `B ⊆ Y` with `A ∩ W = W ∩ f⁻¹(B)`, then `A` has an
sc-smooth retraction near `x`, namely `g ∘ r ∘ f` (the text's "`σ⁻¹` maps `A_Ψ ∩ U(x')` onto
`A_Ψ' ∩ U(a')`", p. 785). -/
theorem exists_retraction_of_isScDiffeoOn {A : Set X} {x : X} (hx : x ∈ A) {W : Set X}
    {V : Set Y} {f : X → Y} {g : Y → X} {B : Set Y} (hxW : x ∈ W) (hd : P.IsScDiffeoOn Q f g W V)
    (hB : Q.IsSubMPolyfold B) (hAW : A ∩ W = W ∩ f ⁻¹' B) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ r : X → X, MapsTo r V V ∧ P.IsScSmoothOn P r V ∧
      (∀ x ∈ V, r (r x) = r x) ∧ r '' V = A ∩ V := by
  have hmemA : ∀ y ∈ W, y ∈ A ↔ f y ∈ B := fun y hy => by
    constructor
    · intro hyA
      exact (hAW.subset ⟨hyA, hy⟩).2
    · intro hyB
      exact (hAW.symm.subset ⟨hy, hyB⟩).1
  have hfxB : f x ∈ B := (hmemA x hxW).1 hx
  obtain ⟨V₀, hV₀, hfxV₀, r, -, hrs, hri, hrA⟩ := hB (f x) hfxB
  have hr_eq : ∀ y ∈ B ∩ V₀, r y = y := fun y hy => by
    rw [← hrA] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact hri z hz
  have hr_mem : ∀ y ∈ V₀, r y ∈ B := fun y hy => by
    have h : r y ∈ r '' V₀ := mem_image_of_mem r hy
    rw [hrA] at h
    exact h.1
  have hVo : IsOpen V := hd.isScSmoothOn_inv.isOpen
  set U := (V ∩ V₀) ∩ r ⁻¹' (V ∩ V₀) with hU
  have hUo : IsOpen U := (hrs.continuousOn.mono inter_subset_right).isOpen_inter_preimage
    (hVo.inter hV₀) (hVo.inter hV₀)
  set W' := W ∩ f ⁻¹' U with hW'
  have hW'o : IsOpen W' :=
    hd.isScSmoothOn.continuousOn.isOpen_inter_preimage hd.isScSmoothOn.isOpen hUo
  have hfx : f x ∈ U := ⟨⟨hd.mapsTo hxW, hfxV₀⟩, by
    rw [mem_preimage, hr_eq _ ⟨hfxB, hfxV₀⟩]; exact ⟨hd.mapsTo hxW, hfxV₀⟩⟩
  have hrU : ∀ y ∈ W', r (f y) ∈ U := fun y hy =>
    ⟨hy.2.2, by rw [mem_preimage, hri _ hy.2.1.2]; exact hy.2.2⟩
  have hmaps : MapsTo (g ∘ r ∘ f) W' W' := fun y hy => by
    have h1 : r (f y) ∈ V := (hrU y hy).1.1
    refine ⟨hd.mapsTo_inv h1, ?_⟩
    simp only [Function.comp_apply, mem_preimage, hd.right_inv _ h1]
    exact hrU y hy
  refine ⟨W', hW'o, ⟨hxW, hfx⟩, g ∘ r ∘ f, hmaps, ?_, fun y hy => ?_, ?_⟩
  · exact MPolyfold.IsScSmoothOn.comp hd.isScSmoothOn_inv
      (MPolyfold.IsScSmoothOn.comp hrs (hd.isScSmoothOn.mono hW'o inter_subset_left)
        fun y hy => hy.2.1.2) fun y hy => (hrU y hy).1.1
  · simp only [Function.comp_apply, hd.right_inv _ (hrU y hy).1.1, hri _ hy.2.1.2]
  · ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, hmaps hz⟩
      refine (hmemA _ (hmaps hz).1).2 ?_
      simp only [Function.comp_apply, hd.right_inv _ (hrU z hz).1.1]
      exact hr_mem _ hz.2.1.2
    · rintro ⟨hyA, hy⟩
      refine ⟨y, hy, ?_⟩
      simp only [Function.comp_apply]
      rw [hr_eq _ ⟨(hmemA y hy.1).1 hyA, hy.2.1.2⟩, hd.left_inv _ hy.1]

/-- **A local criterion for sub-M-polyfolds**: if near every `x ∈ A` there are an
sc-diffeomorphism `f : W → V` of open sets and a sub-M-polyfold `B ⊆ Y` with
`A ∩ W = W ∩ f⁻¹(B)`, then `A` is a sub-M-polyfold. -/
theorem isSubMPolyfold_of_forall_isScDiffeoOn {A : Set X}
    (h : ∀ x ∈ A, ∃ (W : Set X) (V : Set Y) (f : X → Y) (g : Y → X) (B : Set Y),
      x ∈ W ∧ P.IsScDiffeoOn Q f g W V ∧ Q.IsSubMPolyfold B ∧ A ∩ W = W ∩ f ⁻¹' B) :
    P.IsSubMPolyfold A := fun x hx => by
  obtain ⟨W, V, f, g, B, hxW, hd, hB, hAW⟩ := h x hx
  exact exists_retraction_of_isScDiffeoOn hx hxW hd hB hAW

/-- **The preimage of a sub-M-polyfold under a local sc-diffeomorphism** is a sub-M-polyfold. -/
theorem IsLocalScDiffeo.isSubMPolyfold_preimage {f : X → Y} (hf : P.IsLocalScDiffeo Q f)
    {B : Set Y} (hB : Q.IsSubMPolyfold B) : P.IsSubMPolyfold (f ⁻¹' B) :=
  isSubMPolyfold_of_forall_isScDiffeoOn fun x _ => by
    obtain ⟨W, V, g, hxW, hd⟩ := hf x
    exact ⟨W, V, f, g, B, hxW, hd, hB, inter_comm _ _⟩

/-- The constant map at a smooth point is sc-smooth. -/
theorem isScSmoothMap_const_of_smoothSet {x : X} (hx : x ∈ P.smoothSet) :
    Q.IsScSmoothMap P fun _ : Y => x := by
  obtain ⟨ψ, hψ, hxψ⟩ := P.exists_isChart_mem_source x
  have hsm : ψ x ∈ ψ.model.E.smooth := ψ.model.E.mem_smooth_iff.2 fun k =>
    (P.mem_levelSet_iff hψ hxψ).1 (mem_iInter.1 hx k)
  refine MPolyfold.isScSmoothMap_of_local fun z => ?_
  obtain ⟨φ, hφ, hz⟩ := Q.exists_isChart_mem_source z
  refine ⟨φ, ψ, φ.source, hφ, hψ, φ.isOpen_source, hz, subset_rfl, fun _ _ => hxψ, ?_⟩
  rw [φ.image_source]
  refine ⟨fun _ _ => ψ.mapsTo_model x hxψ, fun R _ => ?_⟩
  exact isScSmooth_const_of_mem_smooth R.isScDomain hsm

/-- **A smooth point is a sub-M-polyfold** (the constant retraction). -/
theorem isSubMPolyfold_singleton {x : X} (hx : x ∈ P.smoothSet) : P.IsSubMPolyfold {x} := by
  rintro a rfl
  refine ⟨univ, isOpen_univ, mem_univ a, fun _ => a, mapsTo_univ _ _,
    isScSmoothMap_const_of_smoothSet hx, fun _ _ => rfl, ?_⟩
  have hne : (univ : Set X).Nonempty := ⟨a, mem_univ a⟩
  rw [hne.image_const, inter_univ]

/-- **A dense set with dense complement is not a sub-M-polyfold**: a retraction `r : V → V` onto
`A ∩ V` is the identity on `A ∩ V`, which is dense in `V`, so `r = id` and `V ⊆ A`. -/
theorem not_isSubMPolyfold_of_dense {A : Set X} (hA : Dense A) (hAc : Dense Aᶜ)
    (hne : A.Nonempty) : ¬ P.IsSubMPolyfold A := by
  intro h
  obtain ⟨a, ha⟩ := hne
  obtain ⟨V, hV, haV, r, hmaps, hrs, hri, hrA⟩ := h a ha
  have hfix : EqOn r id (V ∩ A) := fun y hy => by
    have : y ∈ r '' V := by rw [hrA]; exact ⟨hy.2, hy.1⟩
    obtain ⟨z, hz, rfl⟩ := this
    exact hri z hz
  have hid : EqOn r id V := hfix.of_subset_closure hrs.continuousOn continuousOn_id
    inter_subset_left (hA.open_subset_closure_inter hV)
  obtain ⟨y, hyV, hyA⟩ := hAc.inter_open_nonempty V hV ⟨a, haV⟩
  have : y ∈ r '' V := ⟨y, hyV, hid hyV⟩
  rw [hrA] at this
  exact hyA this.1

end Criteria

section Sigma

variable {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)]
  [∀ i, ParacompactSpace (X i)] (P : ∀ i, MPolyfold (X i))

/-- **A subset of a disjoint union of M-polyfolds is a sub-M-polyfold iff its trace on every
summand is one.** -/
theorem isSubMPolyfold_sigma_iff {A : Set (Σ i, X i)} :
    (sigma P).IsSubMPolyfold A ↔ ∀ i, (P i).IsSubMPolyfold (Sigma.mk i ⁻¹' A) := by
  constructor
  · intro h i
    exact (isLocalScDiffeo_sigmaMk P i).isSubMPolyfold_preimage h
  · intro h p hp
    obtain ⟨i, y⟩ := p
    refine exists_retraction_of_isScDiffeoOn hp (mem_range_self y)
      (isScDiffeoOn_sigmaMk P i y).symm (h i) ?_
    ext p
    constructor
    · rintro ⟨hpA, z, rfl⟩
      exact ⟨mem_range_self z, by simpa using hpA⟩
    · rintro ⟨⟨z, rfl⟩, hz⟩
      exact ⟨by simpa using hz, mem_range_self z⟩

end Sigma

end MPolyfold

/-! ### Saturated sets and functors -/

namespace GroupoidStr

variable {Obj Mor : Type u} (G : GroupoidStr Obj Mor)

/-- For a saturated `A`, `s(φ) ∈ A ⟺ t(φ) ∈ A`. -/
theorem src_mem_iff_tgt_mem_of_isSaturated {A : Set Obj} (hA : G.IsSaturated A) (φ : Mor) :
    G.src φ ∈ A ↔ G.tgt φ ∈ A := by
  refine ⟨G.isSaturated_iff.1 hA φ, fun h => ?_⟩
  have := G.isSaturated_iff.1 hA (G.inv φ)
  rw [G.src_inv, G.tgt_inv] at this
  exact this h

end GroupoidStr

/-- **The preimage of a saturated set under a functor is saturated.** -/
theorem GroupoidFunctor.isSaturated_preimage {Obj Mor : Type u} {Obj' Mor' : Type v}
    {G : GroupoidStr Obj Mor} {H : GroupoidStr Obj' Mor'} (F : GroupoidFunctor G H)
    {A : Set Obj'} (hA : H.IsSaturated A) : G.IsSaturated (F.obj ⁻¹' A) :=
  G.isSaturated_iff.2 fun φ hφ => by
    change F.obj (G.tgt φ) ∈ A
    rw [← F.tgt_mor]
    refine H.isSaturated_iff.1 hA _ ?_
    rw [F.src_mor]
    exact hφ

namespace GCT.PolyfoldConstruction

variable {C : GCT.{u}} (S : C.PolyfoldConstruction)

/-! ### Definitions 17.3.1 and 17.3.2 -/

/-- **2021 Definition 17.3.1, p. 784**: a **subpolyfold** of `C`: a saturated full subcategory,
given by its saturated set `A` of objects, such that for every object `α` of `A` and every
`Ψ ∈ F(α)`, `Ψ : G ⋉ O → C`, the set `A_Ψ = Ψ⁻¹(A) ⊆ O` is a sub-M-polyfold of `O`. -/
def IsSubpolyfold (A : Set C.Obj) : Prop :=
  C.toGroupoidStr.IsSaturated A ∧ ∀ α ∈ A, ∀ Ψ ∈ S.F α, Ψ.P.IsSubMPolyfold (Ψ.obj ⁻¹' A)

/-- **2021 Definition 17.3.2, p. 784** (alternative definition of a subpolyfold): a saturated full
subcategory `A` such that for a suitable sc-smooth model `X_Ψ` (a covering family, p. 752) with
natural equivalence `Γ_Ψ : X_Ψ → C` the preimage `Γ_Ψ⁻¹(A)` is an ep-subgroupoid of `X_Ψ`
(Definition 7.1.21). -/
def IsSubpolyfoldModel (A : Set C.Obj) : Prop :=
  C.toGroupoidStr.IsSaturated A ∧ ∃ c : S.CoveringFamily,
    (S.modelEP c.Ψ).X.IsEpSubgroupoid ((S.modelFunctor c.Ψ).obj ⁻¹' A)

/-! ### The preimage in a model -/

section Model

variable {ι : Type u} (Ψ : ι → S.Unif) {A : Set C.Obj}

/-- `Γ_Ψ⁻¹(A)` is saturated for saturated `A`. -/
theorem isSaturated_preimage_modelFunctor (hA : C.toGroupoidStr.IsSaturated A) :
    (S.modelEP Ψ).X.IsSaturated ((S.modelFunctor Ψ).obj ⁻¹' A) :=
  (S.modelFunctor Ψ).isSaturated_preimage hA

/-- **`Γ_Ψ⁻¹(A)` is a sub-M-polyfold of `X_Ψ = ⊔ O_λ` iff every `A_{Ψ_λ} = A ∩ O_λ` is a
sub-M-polyfold of `O_λ`.** -/
theorem isSubMPolyfold_preimage_modelFunctor_iff :
    (S.modelEP Ψ).X.PObj.IsSubMPolyfold ((S.modelFunctor Ψ).obj ⁻¹' A) ↔
      ∀ i, (Ψ i).1.P.IsSubMPolyfold ((Ψ i).1.obj ⁻¹' A) :=
  MPolyfold.isSubMPolyfold_sigma_iff (fun i : ι => (Ψ i).1.P)

/-- `Γ_Ψ⁻¹(A)` is an ep-subgroupoid iff `A` (saturated) has sub-M-polyfold traces `A_{Ψ_λ}`. -/
theorem isEpSubgroupoid_preimage_modelFunctor_iff (hA : C.toGroupoidStr.IsSaturated A) :
    (S.modelEP Ψ).X.IsEpSubgroupoid ((S.modelFunctor Ψ).obj ⁻¹' A) ↔
      ∀ i, (Ψ i).1.P.IsSubMPolyfold ((Ψ i).1.obj ⁻¹' A) :=
  ⟨fun h => (S.isSubMPolyfold_preimage_modelFunctor_iff Ψ).1 h.isSubMPolyfold,
    fun h => ⟨(S.isSubMPolyfold_preimage_modelFunctor_iff Ψ).2 h,
      S.isSaturated_preimage_modelFunctor Ψ hA⟩⟩

end Model

/-! ### The transfer argument of Proposition 17.3.4 -/

section Transfer

variable {S} {A : Set C.Obj}

/-- **The local argument of the proof of Proposition 17.3.4 (p. 785)**: if every `a' ∈ A_Ψ'` is
the source of some `(a', φ, x) ∈ M(Ψ', Ψ)` with `A_Ψ` a sub-M-polyfold of the domain of `Ψ`, then
`A_Ψ'` is a sub-M-polyfold.  Near `a'`, with a sheet `s : U(a', φ, x) → U(a')` and its inverse
`σ`, `A_Ψ' ∩ U(a') = U(a') ∩ σ⁻¹(t⁻¹(A_Ψ))` by saturation, and `t⁻¹(A_Ψ)` is a sub-M-polyfold of
`M(Ψ', Ψ)` (a preimage under the local sc-diffeomorphism `t`). -/
theorem isSubMPolyfold_of_forall_tr (hA : C.toGroupoidStr.IsSaturated A) (Ψ' : S.Unif)
    (h : ∀ a' ∈ Ψ'.1.obj ⁻¹' A, ∃ (Ψ : S.Unif) (a : S.Tr Ψ' Ψ), a.src = a' ∧
      Ψ.1.P.IsSubMPolyfold (Ψ.1.obj ⁻¹' A)) :
    Ψ'.1.P.IsSubMPolyfold (Ψ'.1.obj ⁻¹' A) := by
  intro a' ha'
  obtain ⟨Ψ, a, rfl, hB⟩ := h a' ha'
  obtain ⟨V, W, σ, haV, hd⟩ := S.isLocalScDiffeo_trSrc Ψ' Ψ a
  refine MPolyfold.exists_retraction_of_isScDiffeoOn ha' (hd.mapsTo haV) hd.symm
    ((S.isLocalScDiffeo_trTgt Ψ' Ψ).isSubMPolyfold_preimage hB) (B :=
      (fun b : S.Tr Ψ' Ψ => b.tgt) ⁻¹' (Ψ.1.obj ⁻¹' A)) ?_
  have key : ∀ y ∈ W, Ψ'.1.obj y ∈ A ↔ Ψ.1.obj (σ y).tgt ∈ A := fun y hy => by
    have hs : (σ y).src = y := hd.right_inv y hy
    have h1 := (σ y).src_mor
    have h2 := (σ y).tgt_mor
    rw [hs] at h1
    simpa only [h1, h2] using C.toGroupoidStr.src_mem_iff_tgt_mem_of_isSaturated hA (σ y).mor
  ext y
  constructor
  · rintro ⟨hyA, hyW⟩
    exact ⟨hyW, (key y hyW).1 hyA⟩
  · rintro ⟨hyW, hy⟩
    exact ⟨(key y hyW).2 hy, hyW⟩

/-- **A covering family transfers to every uniformizer**: if `A_{Ψ_λ}` is a sub-M-polyfold for
every member of a family whose footprints cover `|C|`, then `A_Ψ'` is one for every uniformizer
`Ψ'` of `F` (the direction 17.3.2 ⇒ 17.3.1 of Proposition 17.3.4). -/
theorem isSubMPolyfold_of_isCoveringFamily (hA : C.toGroupoidStr.IsSaturated A) {ι : Type u}
    {Ψ : ι → S.Unif} (hc : S.IsCoveringFamily Ψ)
    (h : ∀ i, (Ψ i).1.P.IsSubMPolyfold ((Ψ i).1.obj ⁻¹' A)) (Ψ' : S.Unif) :
    Ψ'.1.P.IsSubMPolyfold (Ψ'.1.obj ⁻¹' A) :=
  isSubMPolyfold_of_forall_tr hA Ψ' fun a' _ => by
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hc.symm ▸ mem_univ (C.toGroupoidStr.π (Ψ'.1.obj a')))
    obtain ⟨q, hq⟩ := (Ψ i).1.mem_footprint_iff.1 hi
    obtain ⟨φ, hs, ht⟩ := (GroupoidStr.π_eq_π_iff _).1 hq.symm
    exact ⟨Ψ i, S.toTr (⟨a', φ, q, hs, ht⟩ : Ψ'.1.Trans (Ψ i).1), rfl, h i⟩

/-- **Definition 17.3.1 transfers to every uniformizer** when `F(α) ≠ ∅` for the objects `α` of
`A`: at `a'` with `Ψ'(a') ∈ A`, a uniformizer `Ψ ∈ F(Ψ'(a'))` at `Ψ(q) = Ψ'(a')` gives
`(a', 1, q) ∈ M(Ψ', Ψ)`. -/
theorem IsSubpolyfold.isSubMPolyfold (hA : S.IsSubpolyfold A)
    (hF : ∀ α ∈ A, (S.F α).Nonempty) (Ψ' : S.Unif) :
    Ψ'.1.P.IsSubMPolyfold (Ψ'.1.obj ⁻¹' A) :=
  isSubMPolyfold_of_forall_tr hA.1 Ψ' fun a' ha' => by
    obtain ⟨Ψ, hΨ⟩ := hF _ ha'
    obtain ⟨q, hq⟩ := S.isAt _ Ψ hΨ
    refine ⟨⟨Ψ, _, hΨ⟩, S.toTr (⟨a', C.toGroupoidStr.unit (Ψ'.1.obj a'), q,
      C.toGroupoidStr.src_unit _, ?_⟩ : Ψ'.1.Trans Ψ), rfl, hA.2 _ ha' Ψ hΨ⟩
    rw [C.toGroupoidStr.tgt_unit]
    exact hq.symm

end Transfer

/-! ### Remark 17.3.3 and Proposition 17.3.4 -/

variable {S}

/-- **2021 Remark 17.3.3, p. 784**: the choice of the model in Definition 17.3.2 does not matter:
if `Γ_Ψ⁻¹(A)` is an ep-subgroupoid of one model, `Γ_Ψ'⁻¹(A)` is one of every model `X_Ψ'`. -/
theorem remark_17_3_3 {A : Set C.Obj} (hA : S.IsSubpolyfoldModel A) (c' : S.CoveringFamily) :
    (S.modelEP c'.Ψ).X.IsEpSubgroupoid ((S.modelFunctor c'.Ψ).obj ⁻¹' A) := by
  obtain ⟨hsat, c, hc⟩ := hA
  have h := (S.isEpSubgroupoid_preimage_modelFunctor_iff c.Ψ hsat).1 hc
  exact (S.isEpSubgroupoid_preimage_modelFunctor_iff c'.Ψ hsat).2 fun i =>
    isSubMPolyfold_of_isCoveringFamily hsat c.cover h (c'.Ψ i)

/-- **Remark 17.3.3**: Definition 17.3.2 asks for one model, equivalently for every model of a
covering family (of which there is at least one). -/
theorem isSubpolyfoldModel_iff_forall {A : Set C.Obj} :
    S.IsSubpolyfoldModel A ↔ C.toGroupoidStr.IsSaturated A ∧ Nonempty S.CoveringFamily ∧
      ∀ c : S.CoveringFamily,
        (S.modelEP c.Ψ).X.IsEpSubgroupoid ((S.modelFunctor c.Ψ).obj ⁻¹' A) :=
  ⟨fun h => ⟨h.1, ⟨h.2.choose⟩, remark_17_3_3 h⟩, fun ⟨h₁, ⟨c⟩, h₃⟩ => ⟨h₁, c, h₃ c⟩⟩

/-- **Proposition 17.3.4, the direction 17.3.2 ⇒ 17.3.1** (no hypothesis): the text's local
argument with a transition `(a', φ', x') ∈ M(Ψ', Ψ)`. -/
theorem isSubpolyfold_of_isSubpolyfoldModel {A : Set C.Obj} (hA : S.IsSubpolyfoldModel A) :
    S.IsSubpolyfold A := by
  obtain ⟨hsat, c, hc⟩ := hA
  have h := (S.isEpSubgroupoid_preimage_modelFunctor_iff c.Ψ hsat).1 hc
  exact ⟨hsat, fun α _ Ψ hΨ => isSubMPolyfold_of_isCoveringFamily hsat c.cover h ⟨Ψ, α, hΨ⟩⟩

/-- **Proposition 17.3.4** in the form with the hypotheses used: if the footprints of `F` cover
`|C|` (so that models exist) and `F(α) ≠ ∅` for the objects of `A`, Definitions 17.3.1 and
17.3.2 are equivalent. -/
theorem proposition_17_3_4_of_nonempty {A : Set C.Obj} (hc : S.HasCoveringUniformizers)
    (hF : ∀ α ∈ A, (S.F α).Nonempty) : S.IsSubpolyfold A ↔ S.IsSubpolyfoldModel A := by
  refine ⟨fun h => ?_, isSubpolyfold_of_isSubpolyfoldModel⟩
  obtain ⟨c⟩ := S.toUniformizerConstruction.exists_coveringFamily_iff.2 hc
  exact ⟨h.1, c, (S.isEpSubgroupoid_preimage_modelFunctor_iff c.Ψ h.1).2 fun i =>
    h.isSubMPolyfold hF (c.Ψ i)⟩

/-- **2021 Proposition 17.3.4, p. 784**: Definition 17.3.1 and Definition 17.3.2 are equivalent,
under the text's tacit `F(α) ≠ ∅` (`HasUniformizers`, as in the choice of covering families,
p. 752). -/
theorem proposition_17_3_4 (hS : S.HasUniformizers) (A : Set C.Obj) :
    S.IsSubpolyfold A ↔ S.IsSubpolyfoldModel A :=
  proposition_17_3_4_of_nonempty
    (S.toUniformizerConstruction.hasCoveringUniformizers_of_hasUniformizers hS)
    fun α _ => hS α

/-- **Both definitions are equivalent to the condition on all uniformizers**: `A` is saturated
and `A_Ψ` is a sub-M-polyfold for every uniformizer `Ψ` of `F` (under `F(α) ≠ ∅`). -/
theorem isSubpolyfold_iff_forall_unif (hS : S.HasUniformizers) (A : Set C.Obj) :
    S.IsSubpolyfold A ↔ C.toGroupoidStr.IsSaturated A ∧
      ∀ Ψ : S.Unif, Ψ.1.P.IsSubMPolyfold (Ψ.1.obj ⁻¹' A) :=
  ⟨fun h => ⟨h.1, h.isSubMPolyfold fun α _ => hS α⟩,
    fun h => ⟨h.1, fun α _ Ψ hΨ => h.2 ⟨Ψ, α, hΨ⟩⟩⟩

/-! ### Smaller uniformizer sets -/

variable (S) in
/-- The uniformizer of `F` underlying a uniformizer of `F' ⊆ F`. -/
def unifOfSubset {F' : C.Obj → Set C.LocalUniformizer} (hF' : ∀ α, F' α ⊆ S.F α)
    (Ψ : GCT.Unif F') : S.Unif :=
  ⟨Ψ.1, Ψ.2.elim fun α h => ⟨α, hF' α h⟩⟩

variable (S) in
/-- **The polyfold structure `(F', M)` for smaller uniformizer sets** `F'(α) ⊆ F(α)`, with the
same transition M-polyfolds. -/
def restrictF (F' : C.Obj → Set C.LocalUniformizer) (hF' : ∀ α, F' α ⊆ S.F α) :
    C.PolyfoldConstruction where
  F := F'
  isAt α Ψ h := S.isAt α Ψ (hF' α h)
  topM Ψ Ψ' := S.topM (S.unifOfSubset hF' Ψ) (S.unifOfSubset hF' Ψ')
  t2M Ψ Ψ' := S.t2M (S.unifOfSubset hF' Ψ) (S.unifOfSubset hF' Ψ')
  paraM Ψ Ψ' := S.paraM (S.unifOfSubset hF' Ψ) (S.unifOfSubset hF' Ψ')
  M Ψ Ψ' := S.M (S.unifOfSubset hF' Ψ) (S.unifOfSubset hF' Ψ')
  isLocalScDiffeo_src Ψ Ψ' := S.isLocalScDiffeo_src (S.unifOfSubset hF' Ψ) (S.unifOfSubset hF' Ψ')
  isLocalScDiffeo_tgt Ψ Ψ' := S.isLocalScDiffeo_tgt (S.unifOfSubset hF' Ψ) (S.unifOfSubset hF' Ψ')
  isScSmoothMap_unit Ψ := S.isScSmoothMap_unit (S.unifOfSubset hF' Ψ)
  isScSmoothMap_inv Ψ Ψ' := S.isScSmoothMap_inv (S.unifOfSubset hF' Ψ) (S.unifOfSubset hF' Ψ')
  isScSmoothMap_mul Ψ Ψ' Ψ'' := S.isScSmoothMap_mul (S.unifOfSubset hF' Ψ)
    (S.unifOfSubset hF' Ψ') (S.unifOfSubset hF' Ψ'')

/-! ### Witnesses -/

section Witnesses

open EpGroupoid.Examples

/-- `0` is a smooth point of `ℝ`. -/
theorem rn_one_zero_mem_smoothSet : (0 : Fin 1 → ℝ) ∈ (rnPolyfold 1).smoothSet :=
  MPolyfold.maxLevel_eq_top_iff.1 (rnPolyfold_maxLevel 1 0)

/-- `{0}` is saturated in `ℤ/2 ⋉ ℝ`. -/
theorem reflection_isSaturated_zero :
    GCT.reflection.toGroupoidStr.IsSaturated ({0} : Set (Fin 1 → ℝ)) :=
  GCT.reflection.toGroupoidStr.isSaturated_iff.2 fun φ hφ => by
    change φ.1 • φ.2 = 0
    change φ.2 = 0 at hφ
    rw [hφ, smul_zero]

/-- **The non-degenerate witness of Definitions 17.3.1, 17.3.2 and Proposition 17.3.4**: in
`C = ℤ/2 ⋉ ℝ` the object `0`, whose isotropy group is `ℤ/2`, is a subpolyfold in both senses;
`A_Ψ = {0}` for the uniformizer `Ψ₀ ∈ F(0)`. -/
theorem reflection_isSubpolyfold_zero :
    reflectionConstruction.IsSubpolyfold ({0} : Set (Fin 1 → ℝ)) ∧
      reflectionConstruction.IsSubpolyfoldModel ({0} : Set (Fin 1 → ℝ)) ∧
      reflectionUnif.1 ∈ reflectionConstruction.F 0 ∧
      ∃ φ ∈ GCT.reflection.toGroupoidStr.mor 0 0, φ ≠ GCT.reflection.toGroupoidStr.unit 0 := by
  have hm : reflectionConstruction.IsSubpolyfoldModel ({0} : Set (Fin 1 → ℝ)) :=
    ⟨reflection_isSaturated_zero, reflectionSingleFamily,
      (reflectionConstruction.isEpSubgroupoid_preimage_modelFunctor_iff _
        reflection_isSaturated_zero).2 fun _ =>
        MPolyfold.isSubMPolyfold_singleton rn_one_zero_mem_smoothSet⟩
  exact ⟨isSubpolyfold_of_isSubpolyfoldModel hm, hm, rfl, GCT.reflection_exists_ne_unit⟩

/-- In `Ψ₀ : ℤ/2 ⋉ ℝ` of the overlap construction, `0` is a smooth point. -/
theorem overlapUnif₀_zero_mem_smoothSet :
    (⟨0, mem_univ _⟩ : (univ : Set (Fin 1 → ℝ))) ∈ overlapUnif₀.1.P.smoothSet :=
  (MPolyfold.isLocalScDiffeo_subtypeVal (P := rnPolyfold 1) isOpen_univ).mem_smoothSet_iff
    ⟨0, mem_univ _⟩ |>.1 rn_one_zero_mem_smoothSet

/-- **The witness with overlapping uniformizers**: for the construction with `Ψ₀ : ℤ/2 ⋉ ℝ`,
`Ψ₁ : ℤ/2 ⋉ (−2, 2)` and `Ψ₂ : {1} ⋉ (1, 3)`, `A = {0}` is a subpolyfold in both senses, and the
transfer of Proposition 17.3.4 makes `A_Ψ` a sub-M-polyfold for every uniformizer `Ψ` (from the
covering family `{Ψ₀}`). -/
theorem overlap_isSubpolyfold_zero :
    overlapConstruction.IsSubpolyfold ({0} : Set (Fin 1 → ℝ)) ∧
      overlapConstruction.IsSubpolyfoldModel ({0} : Set (Fin 1 → ℝ)) ∧
      ∀ Ψ : overlapConstruction.Unif, Ψ.1.P.IsSubMPolyfold (Ψ.1.obj ⁻¹' {0}) := by
  have h0 : ∀ i : overlapSingleFamily.ι, (overlapSingleFamily.Ψ i).1.P.IsSubMPolyfold
      ((overlapSingleFamily.Ψ i).1.obj ⁻¹' ({0} : Set (Fin 1 → ℝ))) := fun i => by
    have he : (overlapSingleFamily.Ψ i).1.obj ⁻¹' ({0} : Set (Fin 1 → ℝ)) =
        ({⟨0, mem_univ _⟩} : Set (univ : Set (Fin 1 → ℝ))) := by
      ext x
      simp only [mem_preimage, mem_singleton_iff]
      exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩
    rw [he]
    exact MPolyfold.isSubMPolyfold_singleton overlapUnif₀_zero_mem_smoothSet
  have hm : overlapConstruction.IsSubpolyfoldModel ({0} : Set (Fin 1 → ℝ)) :=
    ⟨reflection_isSaturated_zero, overlapSingleFamily,
      (overlapConstruction.isEpSubgroupoid_preimage_modelFunctor_iff _
        reflection_isSaturated_zero).2 h0⟩
  exact ⟨isSubpolyfold_of_isSubpolyfoldModel hm, hm,
    isSubMPolyfold_of_isCoveringFamily reflection_isSaturated_zero overlapSingleFamily.cover h0⟩

/-- The rational points `{x | x ∈ ℚ}` of `ℝ`. -/
def ratPoints : Set (Fin 1 → ℝ) := {x | x 0 ∈ range ((↑) : ℚ → ℝ)}

theorem dense_ratPoints : Dense ratPoints :=
  Rat.denseRange_cast.preimage (isOpenMap_eval 0)

theorem dense_compl_ratPoints : Dense ratPointsᶜ :=
  dense_irrational.preimage (isOpenMap_eval 0)

/-- The rational points are saturated in `ℤ/2 ⋉ ℝ` (`x ∈ ℚ ⟺ −x ∈ ℚ`). -/
theorem reflection_isSaturated_ratPoints :
    GCT.reflection.toGroupoidStr.IsSaturated ratPoints :=
  GCT.reflection.toGroupoidStr.isSaturated_iff.2 fun φ hφ => by
    change φ.2 0 ∈ range ((↑) : ℚ → ℝ) at hφ
    change (φ.1 • φ.2) 0 ∈ range ((↑) : ℚ → ℝ)
    obtain ⟨r, hr⟩ := hφ
    rcases Int.units_eq_one_or φ.1 with h | h
    · exact ⟨r, by rw [h, one_smul, hr]⟩
    · exact ⟨-r, by rw [h, Pi.smul_apply, Units.neg_smul, one_smul, ← hr, Rat.cast_neg]⟩

/-- The rational points are not a sub-M-polyfold of `ℝ`. -/
theorem not_isSubMPolyfold_ratPoints : ¬ (rnPolyfold 1).IsSubMPolyfold ratPoints :=
  MPolyfold.not_isSubMPolyfold_of_dense dense_ratPoints dense_compl_ratPoints
    ⟨0, 0, by rw [Rat.cast_zero]; rfl⟩

/-- **Definition 17.3.1 is not satisfied by every saturated set**: the rational points of
`ℤ/2 ⋉ ℝ` are saturated but not a subpolyfold. -/
theorem reflection_not_isSubpolyfold_rat : ¬ reflectionConstruction.IsSubpolyfold ratPoints :=
  fun h => not_isSubMPolyfold_ratPoints (h.2 0 ⟨0, by rw [Rat.cast_zero]; rfl⟩ _ rfl)

/-- The uniformizer sets `F'(x) = F(x)` for irrational `x`, `F'(x) = ∅` for rational `x`. -/
def irrationalF : GCT.reflection.Obj → Set GCT.reflection.LocalUniformizer :=
  fun x => {Ψ | x ∉ ratPoints ∧ Ψ ∈ reflectionConstruction.F x}

/-- The polyfold structure `(F', M)` of `ℤ/2 ⋉ ℝ` without uniformizers at the rational points. -/
def irrationalConstruction : GCT.reflection.PolyfoldConstruction :=
  reflectionConstruction.restrictF irrationalF fun _ _ h => h.2

/-- The tautological uniformizer as a uniformizer of `F'` (it lies in `F'(√2)`). -/
def irrationalUnif : irrationalConstruction.Unif :=
  ⟨reflectionUnif.1, fun _ => Real.sqrt 2, fun h => irrational_sqrt_two h, rfl⟩

/-- **Proposition 17.3.4 with some `F(α)` empty** (why `F(α) ≠ ∅`, the standing reading of §17.1,
is needed): for the polyfold
structure `(F', M)` of `ℤ/2 ⋉ ℝ` with `F'(x) = ∅` exactly at the rational `x` (the footprints of
`F'` still cover `|C|`), the saturated set of rational points satisfies Definition 17.3.1
(vacuously) but not Definition 17.3.2. -/
theorem proposition_17_3_4_empty_family :
    ∃ (S : GCT.reflection.PolyfoldConstruction) (A : Set GCT.reflection.Obj),
      S.HasCoveringUniformizers ∧ S.IsSubpolyfold A ∧ ¬ S.IsSubpolyfoldModel A := by
  refine ⟨irrationalConstruction, ratPoints, ?_, ⟨reflection_isSaturated_ratPoints,
    fun α hα Ψ hΨ => absurd hα hΨ.1⟩, fun h => ?_⟩
  · refine eq_univ_of_forall fun z => mem_iUnion.2 ⟨irrationalUnif, ?_⟩
    change z ∈ reflectionUnif.1.footprint
    rw [reflectionUnif_footprint]
    exact mem_univ z
  · obtain ⟨hsat, c, hc⟩ := h
    have := isSubMPolyfold_of_isCoveringFamily hsat c.cover
      ((irrationalConstruction.isEpSubgroupoid_preimage_modelFunctor_iff c.Ψ hsat).1 hc)
      irrationalUnif
    exact not_isSubMPolyfold_ratPoints this

end Witnesses

end GCT.PolyfoldConstruction

end Polyfold
