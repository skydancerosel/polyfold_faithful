import Polyfold.Chapter17.ProperCoveringUniformizer
import Polyfold.Chapter11.BranchedEquivalenceLocalization

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17, §17.8:
**Proposition 17.8.16** (pp. 839–840, pull-backs of branched ep⁺-subcategories along proper
polyfold covering functors) and the "easy exercise" of its proof (p. 839: the pull-back of a
branched ep⁺-subgroupoid along a proper covering functor of ep-groupoids is branched).  Numbers
and pages are the 2021 text's.

# Branched ep⁺-subcategories and proper coverings

## The text, paraphrased

(Proposition 17.8.16) For a proper polyfold covering functor `P : A → B` and a branched
ep⁺-subcategory `Θ : B → ℚ⁺`, `P^*Θ := Θ ∘ P` is a branched ep⁺-subcategory of `A` (with the
induced structure); (1) manifold-type, (2) orbifold-type, (3) tameness and (4) compactness are
preserved.  *Proof*: with an sc-smooth model `τ̂ : E → X` (17.104), `Θ` is branched iff `Γ^*Θ`
is; "it is an easy exercise" that the pull-back of a branched ep⁺-subgroupoid by a proper
covering functor of ep-groupoids is branched, and `P^*Θ = Γ̂^*(τ̂^*(Γ^*Θ))`.  (2) is clear.
(1): for `φ, φ' : α → α'` between points of the support, `P(φ) = P(φ')`, and Definition
17.8.1 (4) gives `φ = φ'`.  (4): a sequence in `|supp(Θ ∘ P)|` has image converging (after a
subsequence) to `z ∈ |supp(Θ)|`; in a proper covering uniformizer at `β`, `|β| = z`, it is
represented in `O_β` by `o_k → o_β` and lifted to `e_k ∈ E` in one sheet, so it converges.

## What is formalized

* General topology: `paracompactSpace_of_isProperMap` (a space with a proper map onto a
  paracompact space is paracompact; Definition 9.1.2 (1) asks `|supp|` to be paracompact).
* **The easy exercise**, for a proper covering functor `τ : E → X` of ep-groupoids
  (Definition 8.5.1): `IsProperCovering.exists_lift` (lifting of morphisms, from (3)),
  `IsProperCovering.isClosedMap_orbitMap`, `IsProperCovering.finite_orbitMap_fiber`,
  `IsProperCovering.isProperMap_orbitMap` (`|τ|` is a proper map), and
  **`IsProperCovering.isBranchedEpSubgroupoid_pullbackTheta`**; with
  `isManifoldType_pullbackTheta`, `isCompactBranched_pullbackTheta`, and (orbifold-type, closed)
  Chapter 11's `isOrbifoldType_pullbackTheta`, `isClosedBranched_pullbackTheta`, which hold for
  every functor.
* For a proper covering uniformizer: `ProperCoveringUniformizer.finite_fiber`,
  `isProperCovering_τ` (`τ̂` is a proper covering functor, Remark 17.8.5),
  `orbitMap_comm` (`|P| ∘ |Ψ̂| = |Ψ| ∘ |τ̂|`), `comp_hat_eq_pullbackTheta`
  (`Θ ∘ P ∘ Ψ̂ = τ̂^*(Θ ∘ Ψ)`).
* "Branched ep⁺-subcategory" (Definition 17.5.1) for the induced structures:
  `ProperCoveringUniformizerConstruction.IsBranchedBase` (on `B`, through the uniformizers `Ψ`,
  which form the induced uniformizer construction of `B`) and `IsBranchedHat` (on `A`, through
  the `Ψ̂`).
* **Proposition 17.8.16**: `proposition_17_8_16` (branched), `proposition_17_8_16_one`
  (manifold-type), `proposition_17_8_16_two` (orbifold-type), `proposition_17_8_16_four`
  (compactness of `|supp(Θ ∘ P)| ⊆ |A|`), and `orbitSupp_comp_eq_preimage`
  (`|supp(Θ ∘ P)| = |P|⁻¹(|supp(Θ)|)`).
* Witness: `proposition_17_8_16_reflection`: `Θ₀ = 1_{0}` on `ℤˣ ⋉ ℝ` and the two-sheet
  construction; `Θ₀ ∘ P` is branched, compact, of manifold-type, and equal to `1` at the two objects
  `(true, 0)`, `(false, 0)`.

## Readings

* "With the induced structures": the structure of `B` has the uniformizers `Ψ` of the pairs in
  `F(β)` (`toUniformizerConstruction`), and Definition 17.5.1 asks `Θ ∘ Ψ` to be branched for
  them; for `A` the uniformizers are the `Ψ̂ : E → A`, and we read "branched ep⁺-subcategory of
  `A`" as `Θ' ∘ Ψ̂` branched on `E` for every `(Ψ̂, Ψ) ∈ F`.  This is the local form of the
  text's proof (`Γ̂^*(τ̂^*(Γ^*Θ))` restricted to one `E_λ`); the global model (17.104) is not
  needed.
* The easy exercise holds for every proper covering functor of Definition 8.5.1; the paracompactness
  of `|supp(τ^*Θ)| = |τ|⁻¹(|supp(Θ)|)` (Definition 9.1.2 (1)), which the text does not mention,
  follows from `|τ|` being a proper map (closed with finite fibres).
* (4) needs a proper covering uniformizer at the points of `supp(Θ)` ("we take a proper covering
  uniformizer around `β`"): the hypothesis `unif_hyp`, the standing reading `F(β) ≠ ∅`.  The
  sequence argument is replaced by ultrafilters: `|τ̂|` is a proper map, so no metrizability is
  needed.
* (1) and (2) are statements about `Θ` on `B` and `Θ ∘ P` on `A` (Definition 17.5.4); they use
  only Definition 17.8.1 (4).
* (3) (tameness) is in `ProperCoveringTame.lean` (`proposition_17_8_16_three`).
-/

open Set Function Topology Filter

noncomputable section

namespace Polyfold

open EpGroupoid.Examples

universe u v w

/-! ### A proper map onto a paracompact space -/

section Topology

variable {X : Type v} {Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]

/-- **A perfect preimage of a paracompact space is paracompact**: if `f : X → Y` is a proper map
and `Y` is paracompact, then `X` is paracompact.  For `y ∈ Y` the compact fibre `f⁻¹(y)` lies in a
finite union `W(y)` of members of the cover; `V(y) = Y ∖ f(X ∖ W(y))` is an open neighbourhood of
`y` with `f⁻¹(V(y)) ⊆ W(y)`; a locally finite refinement of the `V(y)` pulls back, intersected with
the members, to a locally finite refinement. -/
theorem paracompactSpace_of_isProperMap [ParacompactSpace Y] {f : X → Y} (hf : IsProperMap f) :
    ParacompactSpace X := by
  refine ⟨fun α s hso hsc => ?_⟩
  have hcov : ∀ y : Y, ∃ I : Finset α, f ⁻¹' {y} ⊆ ⋃ a ∈ I, s a := fun y =>
    (hf.isCompact_preimage isCompact_singleton).elim_finite_subcover s hso
      (hsc ▸ subset_univ _)
  choose I hI using hcov
  set V : Y → Set Y := fun y => (f '' (⋃ a ∈ I y, s a)ᶜ)ᶜ with hVdef
  have hVo : ∀ y, IsOpen (V y) := fun y =>
    (hf.isClosedMap _ (isOpen_biUnion fun a _ => hso a).isClosed_compl).isOpen_compl
  have hyV : ∀ y, y ∈ V y := fun y ⟨x, hx, hxy⟩ => hx (hI y hxy)
  have hVW : ∀ y, f ⁻¹' V y ⊆ ⋃ a ∈ I y, s a := fun y x hx => by
    by_contra h
    exact hx ⟨x, h, rfl⟩
  obtain ⟨W, hWo, hWc, hWlf, hWV⟩ := precise_refinement V hVo
    (eq_univ_of_forall fun y => mem_iUnion.2 ⟨y, hyV y⟩)
  set T : Set (Set X) := ⋃ y, (fun a => f ⁻¹' W y ∩ s a) '' (I y : Set α) with hT
  have hmemT : ∀ {t : Set X}, t ∈ T → ∃ y, ∃ a ∈ I y, f ⁻¹' W y ∩ s a = t := by
    intro t ht
    simp only [hT, mem_iUnion, mem_image, Finset.mem_coe] at ht
    exact ht
  refine ⟨T, Subtype.val, ?_, ?_, ?_, ?_⟩
  · rintro ⟨t, ht⟩
    obtain ⟨y, a, -, rfl⟩ := hmemT ht
    exact ((hWo y).preimage hf.continuous).inter (hso a)
  · refine eq_univ_of_forall fun x => ?_
    obtain ⟨y, hy⟩ := mem_iUnion.1 (hWc.symm ▸ mem_univ (f x) : f x ∈ ⋃ y, W y)
    have hx := hVW y (hWV y hy)
    simp only [mem_iUnion, exists_prop] at hx
    obtain ⟨a, ha, hxa⟩ := hx
    refine mem_iUnion.2 ⟨⟨f ⁻¹' W y ∩ s a, ?_⟩, hy, hxa⟩
    simp only [hT, mem_iUnion, mem_image, Finset.mem_coe]
    exact ⟨y, a, ha, rfl⟩
  · intro x
    obtain ⟨N, hN, hNf⟩ := hWlf (f x)
    refine ⟨f ⁻¹' N, hf.continuous.continuousAt.preimage_mem_nhds hN, ?_⟩
    have hfinT : (⋃ y ∈ {y | (W y ∩ N).Nonempty},
        (fun a => f ⁻¹' W y ∩ s a) '' (I y : Set α)).Finite :=
      hNf.biUnion fun y _ => (I y).finite_toSet.image _
    refine (hfinT.preimage Subtype.val_injective.injOn).subset ?_
    rintro ⟨t, ht⟩ ⟨z, hzt, hzN⟩
    obtain ⟨y, a, ha, rfl⟩ := hmemT ht
    simp only [mem_preimage, mem_iUnion, mem_image, Finset.mem_coe, exists_prop]
    exact ⟨y, ⟨f z, hzt.1, hzN⟩, a, ha, rfl⟩
  · rintro ⟨t, ht⟩
    obtain ⟨y, a, -, rfl⟩ := hmemT ht
    exact ⟨a, inter_subset_right⟩

/-- The restriction of a proper map to the preimage of a subset is proper. -/
theorem isProperMap_restrictPreimage {f : X → Y} (hf : IsProperMap f) (K : Set Y) :
    IsProperMap (K.restrictPreimage f) := by
  refine isProperMap_iff_isClosedMap_and_compact_fibers.2
    ⟨hf.continuous.restrictPreimage, hf.isClosedMap.restrictPreimage K, fun k => ?_⟩
  have h : K.restrictPreimage f ⁻¹' {k} = ((↑) : f ⁻¹' K → X) ⁻¹' (f ⁻¹' {k.1}) := by
    ext x
    simp [Set.restrictPreimage, Subtype.ext_iff]
  rw [h]
  exact IsInducing.subtypeVal.isCompact_preimage' (hf.isCompact_preimage isCompact_singleton)
    fun x hx => ⟨⟨x, by
      have : f x = k.1 := hx
      change f x ∈ K
      rw [this]
      exact k.2⟩, rfl⟩

end Topology

/-! ### The easy exercise: pull-backs along proper covering functors of ep-groupoids -/

section EpLevel

variable {ObjE MorE ObjX MorX : Type u} [TopologicalSpace ObjE] [T2Space ObjE]
  [ParacompactSpace ObjE] [TopologicalSpace MorE] [T2Space MorE] [ParacompactSpace MorE]
  [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {E : EpGroupoid ObjE MorE} {X : EpGroupoid ObjX MorX} {τ : EpFunctor E X}

namespace EpFunctor.IsProperCovering

variable (hτ : τ.IsProperCovering)
include hτ

/-- **Lifting of morphisms** (Definition 8.5.1 (3)): a morphism `φ` of `X` with `s(φ) = τ(e)` is
`τ(ψ)` for a `ψ` with `s(ψ) = e`. -/
theorem exists_lift {φ : MorX} {e : ObjE} (h : X.src φ = τ.obj e) :
    ∃ ψ : MorE, τ.mor ψ = φ ∧ E.src ψ = e := by
  let := MPolyfold.paracompactSpace_prod X.PMor E.PObj
  let := (X.PMor.prod E.PObj).paracompactSpace_subtype (MPolyfold.fibredProduct X.src τ.obj)
  obtain ⟨g, hg⟩ := hτ.isScDiffeo_fibredMap
  have := hg.right_inv ⟨(φ, e), h⟩ (mem_univ _)
  exact ⟨g ⟨(φ, e), h⟩, congrArg (fun q : MPolyfold.fibredProduct X.src τ.obj =>
    (q : MorX × ObjE).1) this, congrArg (fun q : MPolyfold.fibredProduct X.src τ.obj =>
    (q : MorX × ObjE).2) this⟩

/-- `ψ ↦ (τ(ψ), s(ψ))` is injective (Definition 8.5.1 (3)). -/
theorem injective_fibredMap : Injective τ.fibredMap := by
  let := MPolyfold.paracompactSpace_prod X.PMor E.PObj
  let := (X.PMor.prod E.PObj).paracompactSpace_subtype (MPolyfold.fibredProduct X.src τ.obj)
  obtain ⟨g, hg⟩ := hτ.isScDiffeo_fibredMap
  intro a b h
  rw [← hg.left_inv a (mem_univ _), ← hg.left_inv b (mem_univ _), h]

/-- Over `π(x)`, every orbit of `E` meets `τ⁻¹(x)`. -/
theorem exists_mem_fiber_of_orbitMap {e : ObjE} {x : ObjX}
    (h : τ.orbitMap (E.π e) = X.π x) : ∃ e', τ.obj e' = x ∧ E.π e' = E.π e := by
  obtain ⟨φ, hs, ht⟩ := (X.π_eq_π_iff).1 (h.symm.trans (τ.orbitMap_π e)).symm
  obtain ⟨ψ, hψ, hψs⟩ := hτ.exists_lift hs
  refine ⟨E.tgt ψ, ?_, ?_⟩
  · rw [← τ.tgt_mor, hψ, ht]
  · exact (E.π_eq_π_iff).2 ⟨ψ, hψs, rfl⟩ |>.symm

/-- `π_X⁻¹(|τ|(C)) = τ(π_E⁻¹(C))`. -/
theorem preimage_π_image_orbitMap (C : Set E.OrbitSpace) :
    X.π ⁻¹' (τ.orbitMap '' C) = τ.obj '' (E.π ⁻¹' C) := by
  ext x
  constructor
  · rintro ⟨c, hc, hcx⟩
    obtain ⟨e, rfl⟩ := E.surjective_π c
    obtain ⟨e', he', hee'⟩ := hτ.exists_mem_fiber_of_orbitMap hcx
    exact ⟨e', by rw [mem_preimage, hee']; exact hc, he'⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨E.π e, he, τ.orbitMap_π e⟩

/-- **`|τ|` is a closed map.**  For `x ∉ τ(Ĉ)` (`Ĉ = π_E⁻¹(C)`), with the evenly covered
neighbourhood `U(x)` and the sheets `V(e)`, `e ∈ τ⁻¹(x)`, the open set
`⋂_e U(x) ∩ σ_e⁻¹(V(e) ∖ Ĉ)` contains `x` and misses `τ(Ĉ)`. -/
theorem isClosedMap_orbitMap : IsClosedMap τ.orbitMap := by
  intro C hC
  rw [← isQuotientMap_quotient_mk'.isClosed_preimage]
  change IsClosed (X.π ⁻¹' (τ.orbitMap '' C))
  rw [hτ.preimage_π_image_orbitMap C]
  set Ĉ := E.π ⁻¹' C with hĈ
  have hĈc : IsClosed Ĉ := hC.preimage E.continuous_π
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨U, V, σ, hUo, hxU, -, hV, hpre⟩ := hτ.evenlyCovered x
  have hfin := hτ.finite_fiber x
  set N : Set ObjX := U ∩ ⋂ e ∈ τ.obj ⁻¹' {x}, (U ∩ σ e ⁻¹' (V e \ Ĉ)) with hN
  refine ⟨N, ?_, ?_, ?_⟩
  · rintro n ⟨hnU, hn⟩ ⟨c, hcĈ, rfl⟩
    have hc : c ∈ τ.obj ⁻¹' U := hnU
    rw [hpre] at hc
    simp only [mem_iUnion, exists_prop] at hc
    obtain ⟨e, he, hce⟩ := hc
    have h1 := (mem_iInter₂.1 hn) e he
    have h2 : σ e (τ.obj c) = c := ((hV e he).2).left_inv c hce
    rw [mem_inter_iff, mem_preimage, h2] at h1
    exact h1.2.2 hcĈ
  · refine hUo.inter (hfin.isOpen_biInter fun e he => ?_)
    have hd := (hV e he).2
    exact hd.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage hUo
      (hd.isScSmoothOn.isOpen.sdiff hĈc)
  · refine ⟨hxU, mem_iInter₂.2 fun e he => ⟨hxU, ?_⟩⟩
    have hd := (hV e he).2
    have he' : τ.obj e = x := he
    have h2 : σ e x = e := by rw [← he']; exact hd.left_inv e (hV e he).1
    rw [mem_preimage, h2]
    exact ⟨(hV e he).1, fun heĈ => hx ⟨e, heĈ, he'⟩⟩

/-- The fibres of `|τ|` are finite: `|τ|⁻¹(|x|) = π_E(τ⁻¹(x))`. -/
theorem finite_orbitMap_fiber (z : X.OrbitSpace) : (τ.orbitMap ⁻¹' {z}).Finite := by
  obtain ⟨x, rfl⟩ := X.surjective_π z
  refine ((hτ.finite_fiber x).image E.π).subset ?_
  intro c hc
  obtain ⟨e, rfl⟩ := E.surjective_π c
  obtain ⟨e', he', hee'⟩ := hτ.exists_mem_fiber_of_orbitMap hc
  exact ⟨e', he', hee'⟩

/-- **`|τ| : |E| → |X|` is a proper map** (closed with finite fibres). -/
theorem isProperMap_orbitMap : IsProperMap τ.orbitMap :=
  isProperMap_iff_isClosedMap_and_compact_fibers.2
    ⟨τ.continuous_orbitMap, hτ.isClosedMap_orbitMap,
      fun z => (hτ.finite_orbitMap_fiber z).isCompact⟩

/-- **The easy exercise of the proof of Proposition 17.8.16** (p. 839): the pull-back
`τ^*Θ' = Θ' ∘ τ` of a branched ep⁺-subgroupoid along a proper covering functor of ep-groupoids
(Definition 8.5.1) is a branched ep⁺-subgroupoid (Definition 9.1.2).  The local branching
structures are moved by the local inverses of `τ` (as for equivalences, Theorem 11.3.3);
`|supp(τ^*Θ')| = |τ|⁻¹(|supp(Θ')|)` is paracompact because `|τ|` is a proper map. -/
theorem isBranchedEpSubgroupoid_pullbackTheta {Θ' : ObjX → ℚ}
    (hΘ' : X.IsBranchedEpSubgroupoid Θ') : E.IsBranchedEpSubgroupoid (τ.pullbackTheta Θ') where
  nonneg _ := hΘ'.nonneg _
  isFunctorial := τ.isFunctorial_pullbackTheta hΘ'.isFunctorial
  support_subset x hx := (hτ.isLocalScDiffeo.mem_smoothSet_iff x).1 (hΘ'.support_subset hx)
  paracompactSpace_orbitSupp := by
    rw [τ.orbitSupp_pullbackTheta hΘ'.isFunctorial]
    have := hΘ'.paracompactSpace_orbitSupp
    exact paracompactSpace_of_isProperMap (isProperMap_restrictPreimage hτ.isProperMap_orbitMap _)
  localBranching x hx := by
    obtain ⟨B'⟩ := hΘ'.localBranching _ hx
    obtain ⟨U, V, g, hxU, hd⟩ := hτ.isLocalScDiffeo x
    exact ⟨B'.mapDiffeo hd.symm (hd.mapsTo hxU) (hd.left_inv x hxU) fun z hz => by
      simp only [EpFunctor.pullbackTheta_apply, hd.right_inv z hz]⟩

/-- Manifold-type (Definition 9.1.8 (1)) is preserved by the pull-back along a proper covering
functor: two morphisms with the same source and the same image are equal (Definition 8.5.1 (3)). -/
theorem isManifoldType_pullbackTheta {Θ' : ObjX → ℚ} (h : X.IsManifoldType Θ') :
    E.IsManifoldType (τ.pullbackTheta Θ') := by
  refine ⟨EpFunctor.isOrbifoldType_pullbackTheta τ h.1, fun φ φ' hs ht hss htt => ?_⟩
  have hm : τ.mor φ = τ.mor φ' := by
    refine h.2 _ _ ?_ ?_ ?_ ?_
    · rw [τ.src_mor]; exact hs
    · rw [τ.tgt_mor]; exact ht
    · rw [τ.src_mor, τ.src_mor, hss]
    · rw [τ.tgt_mor, τ.tgt_mor, htt]
  exact hτ.injective_fibredMap (Subtype.ext (Prod.ext hm hss))

/-- Compactness (Definition 9.1.6 (2)) is preserved by the pull-back along a proper covering
functor (`|τ|` is a proper map). -/
theorem isCompactBranched_pullbackTheta {Θ' : ObjX → ℚ} (hΘ' : X.IsFunctorial Θ')
    (hc : X.IsCompactBranched Θ') : E.IsCompactBranched (τ.pullbackTheta Θ') := by
  unfold EpGroupoid.IsCompactBranched
  rw [τ.orbitSupp_pullbackTheta hΘ']
  exact hτ.isProperMap_orbitMap.isCompact_preimage hc

end EpFunctor.IsProperCovering

end EpLevel

/-! ### Proper covering uniformizers -/

namespace ProperCoveringUniformizer

variable {A B : GCT.{u}} {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr} {β : B.Obj}
  (U : ProperCoveringUniformizer P β)

/-- The fibre `τ̂⁻¹(o_β)` is finite: it is in bijection with `P⁻¹(β)` (Definition 17.8.10 (1)),
which is finite (Definition 17.8.1 (2)). -/
theorem finite_fiber (hPc : P.IsProperCoveringGCT) : U.model.fiber.Finite :=
  Set.Finite.of_finite_image (U.bijOn_fiber.image_eq ▸ hPc.finite_fiber β) U.bijOn_fiber.injOn

/-- **`τ̂ : E → G ⋉ O_β` is a proper covering functor** (Definition 8.5.1; Remark 17.8.5). -/
theorem isProperCovering_τ (hPc : P.IsProperCoveringGCT) : U.τ.IsProperCovering :=
  U.model.isProperCovering (U.finite_fiber hPc)

/-- `|P| ∘ |Ψ̂| = |Ψ| ∘ |τ̂|` on orbit spaces. -/
theorem orbitMap_comm (c : U.E.OrbitSpace) :
    P.orbitMap (U.hat.orbitMap c) = U.Ψ.functor.orbitMap (U.τ.orbitMap c) := by
  obtain ⟨e, rfl⟩ := U.E.surjective_π c
  change B.toGroupoidStr.π (P.obj (U.hat.obj e)) = B.toGroupoidStr.π (U.Ψ.obj (U.τ.obj e))
  rw [U.obj_comm]

/-- `Θ ∘ P ∘ Ψ̂ = τ̂^*(Θ ∘ Ψ)` (from `P ∘ Ψ̂ = Ψ ∘ τ̂`). -/
theorem comp_hat_eq_pullbackTheta (Θ : B.Obj → ℚ) :
    (Θ ∘ P.obj) ∘ U.hat.obj = U.τ.pullbackTheta (Θ ∘ U.Ψ.obj) := by
  funext e
  simp only [comp_apply, EpFunctor.pullbackTheta_apply]
  rw [U.obj_comm]

end ProperCoveringUniformizer

/-! ### Branched ep⁺-subcategories for the induced structures -/

namespace ProperCoveringUniformizerConstruction

variable {A B : GCT.{u}} {P : GroupoidFunctor A.toGroupoidStr B.toGroupoidStr}
  (F : ProperCoveringUniformizerConstruction P)

/-- **Definition 17.5.1 for the induced structure of `B`**: `Θ : B → ℚ⁺` is a functor and
`Θ ∘ Ψ` is a branched ep⁺-subgroupoid of `G ⋉ O_β` for every `(Ψ̂, Ψ) ∈ F(β)` (the uniformizers
`Ψ` form the induced uniformizer construction `toUniformizerConstruction`). -/
structure IsBranchedBase (Θ : B.Obj → ℚ) : Prop where
  nonneg : ∀ β, 0 ≤ Θ β
  isFunctorial : ∀ φ : B.Mor, Θ (B.toGroupoidStr.src φ) = Θ (B.toGroupoidStr.tgt φ)
  isBranched : ∀ β, ∀ U ∈ F.F β, U.Ψ.ep.IsBranchedEpSubgroupoid (Θ ∘ U.Ψ.obj)

/-- **Definition 17.5.1 for the induced structure of `A`** (the uniformizers `Ψ̂ : E → A`):
`Θ' : A → ℚ⁺` is a functor and `Θ' ∘ Ψ̂` is a branched ep⁺-subgroupoid of `E` for every
`(Ψ̂, Ψ) ∈ F(β)`. -/
structure IsBranchedHat (Θ' : A.Obj → ℚ) : Prop where
  nonneg : ∀ α, 0 ≤ Θ' α
  isFunctorial : ∀ φ : A.Mor, Θ' (A.toGroupoidStr.src φ) = Θ' (A.toGroupoidStr.tgt φ)
  isBranched : ∀ β, ∀ U ∈ F.F β, U.E.IsBranchedEpSubgroupoid (Θ' ∘ U.hat.obj)

variable {F}

/-- **Proposition 17.8.16**, pp. 839–840: for a proper covering functor `P` with a proper covering
uniformizer construction `F` and a branched ep⁺-subcategory `Θ` of `B`, the pull-back
`P^*Θ = Θ ∘ P` is a branched ep⁺-subcategory of `A`: `Θ ∘ P ∘ Ψ̂ = τ̂^*(Θ ∘ Ψ)` and `τ̂` is a
proper covering functor of ep-groupoids (the easy exercise). -/
theorem proposition_17_8_16 (hPc : P.IsProperCoveringGCT) {Θ : B.Obj → ℚ}
    (hΘ : F.IsBranchedBase Θ) : F.IsBranchedHat (Θ ∘ P.obj) where
  nonneg _ := hΘ.nonneg _
  isFunctorial φ := by
    change Θ (P.obj (A.toGroupoidStr.src φ)) = Θ (P.obj (A.toGroupoidStr.tgt φ))
    rw [← P.src_mor, ← P.tgt_mor]
    exact hΘ.isFunctorial _
  isBranched β U hU := by
    rw [U.comp_hat_eq_pullbackTheta]
    exact (U.isProperCovering_τ hPc).isBranchedEpSubgroupoid_pullbackTheta
      (hΘ.isBranched β U hU)

/-- **Proposition 17.8.16 (1)**: if `Θ` is of manifold-type (values `0`, `1`; at most one
morphism between two objects of `supp(Θ)`), so is `Θ ∘ P`.  *Proof*: `P(φ) = P(φ')` and
Definition 17.8.1 (4). -/
theorem proposition_17_8_16_one (hPc : P.IsProperCoveringGCT) {Θ : B.Obj → ℚ}
    (h01 : ∀ β, Θ β = 0 ∨ Θ β = 1)
    (hmor : ∀ ψ ψ' : B.Mor, 0 < Θ (B.toGroupoidStr.src ψ) → 0 < Θ (B.toGroupoidStr.tgt ψ) →
      B.toGroupoidStr.src ψ = B.toGroupoidStr.src ψ' →
      B.toGroupoidStr.tgt ψ = B.toGroupoidStr.tgt ψ' → ψ = ψ') :
    (∀ α, Θ (P.obj α) = 0 ∨ Θ (P.obj α) = 1) ∧
      ∀ φ φ' : A.Mor, 0 < Θ (P.obj (A.toGroupoidStr.src φ)) →
        0 < Θ (P.obj (A.toGroupoidStr.tgt φ)) →
        A.toGroupoidStr.src φ = A.toGroupoidStr.src φ' →
        A.toGroupoidStr.tgt φ = A.toGroupoidStr.tgt φ' → φ = φ' := by
  refine ⟨fun α => h01 _, fun φ φ' hs ht hss htt => ?_⟩
  refine ProperCoveringUniformizer.eq_of_mor_eq_of_src_eq hPc (hmor _ _ ?_ ?_ ?_ ?_) hss
  · rw [P.src_mor]; exact hs
  · rw [P.tgt_mor]; exact ht
  · rw [P.src_mor, P.src_mor, hss]
  · rw [P.tgt_mor, P.tgt_mor, htt]

/-- **Proposition 17.8.16 (2)**: if `Θ` only takes the values `0` and `1`, so does `Θ ∘ P`. -/
theorem proposition_17_8_16_two {Θ : B.Obj → ℚ} (h01 : ∀ β, Θ β = 0 ∨ Θ β = 1) :
    ∀ α, Θ (P.obj α) = 0 ∨ Θ (P.obj α) = 1 := fun _ => h01 _

/-- `|supp(Θ ∘ P)| = |P|⁻¹(|supp(Θ)|)` for a functor `Θ`. -/
theorem orbitSupp_comp_eq_preimage {Θ : B.Obj → ℚ}
    (hΘ : ∀ φ : B.Mor, Θ (B.toGroupoidStr.src φ) = Θ (B.toGroupoidStr.tgt φ)) :
    A.toGroupoidStr.π '' {α | 0 < Θ (P.obj α)} =
      P.orbitMap ⁻¹' (B.toGroupoidStr.π '' {β | 0 < Θ β}) := by
  ext a
  obtain ⟨α, rfl⟩ := A.toGroupoidStr.surjective_π a
  constructor
  · rintro ⟨α', hα', hαα'⟩
    refine ⟨P.obj α', hα', ?_⟩
    rw [← P.orbitMap_π, hαα']
  · rintro ⟨β', hβ', hβα⟩
    refine ⟨α, ?_, rfl⟩
    rw [P.orbitMap_π] at hβα
    obtain ⟨ψ, hs, ht⟩ := (B.toGroupoidStr.π_eq_π_iff).1 hβα
    change 0 < Θ (P.obj α)
    rw [← ht, ← hΘ ψ, hs]
    exact hβ'

/-- **Proposition 17.8.16 (4)**: if `|supp(Θ)| ⊆ |B|` is compact, so is `|supp(Θ ∘ P)| ⊆ |A|`,
given a proper covering uniformizer at every point of `supp(Θ)` (`unif_hyp`).  *Proof*
(ultrafilters in place of the text's sequences): an ultrafilter `𝒰` on `|P|⁻¹(|supp Θ|)` has
`|P|(𝒰) → z`; in a proper covering uniformizer at `β`, `|β| = z`, `𝒰` comes from an
ultrafilter `𝒱` on `|E|` with `|τ̂|(𝒱) → |o_β|`;
`|τ̂|` is proper, so `𝒱` converges, and so does `𝒰 = |Ψ̂|(𝒱)`. -/
theorem proposition_17_8_16_four (hPc : P.IsProperCoveringGCT) {Θ : B.Obj → ℚ}
    (hΘ : ∀ φ : B.Mor, Θ (B.toGroupoidStr.src φ) = Θ (B.toGroupoidStr.tgt φ))
    (unif_hyp : ∀ β, 0 < Θ β → (F.F β).Nonempty)
    (hc : IsCompact (B.toGroupoidStr.π '' {β | 0 < Θ β})) :
    IsCompact (A.toGroupoidStr.π '' {α | 0 < Θ (P.obj α)}) := by
  rw [orbitSupp_comp_eq_preimage hΘ]
  set K := B.toGroupoidStr.π '' {β | 0 < Θ β}
  refine isCompact_iff_ultrafilter_le_nhds.2 fun 𝒰 h𝒰 => ?_
  have hmap : (𝒰.map P.orbitMap : Filter B.OrbitSpace) ≤ 𝓟 K := by
    rw [Ultrafilter.coe_map, map_le_iff_le_comap, comap_principal]
    exact h𝒰
  obtain ⟨z, hzK, hz⟩ := hc.ultrafilter_le_nhds _ hmap
  obtain ⟨β, hβ, rfl⟩ := hzK
  obtain ⟨U, -⟩ := unif_hyp β hβ
  obtain ⟨V, hVo, hβV, hΨe, hΨr, hhe, hhr⟩ := U.orbit_homeomorph
  -- `range |Ψ̂| = |P|⁻¹(V)` is in `𝒰`
  have hV𝒰 : P.orbitMap ⁻¹' V ∈ 𝒰 := by
    have : V ∈ (𝒰.map P.orbitMap : Filter B.OrbitSpace) := hz (hVo.mem_nhds hβV)
    exact this
  have hr𝒰 : range U.hat.orbitMap ∈ 𝒰 := hhr ▸ hV𝒰
  set 𝒱 := 𝒰.comap hhe.injective hr𝒰
  have h𝒱 : 𝒱.map U.hat.orbitMap = 𝒰 := Ultrafilter.coe_injective (by
    rw [Ultrafilter.coe_map, Ultrafilter.coe_comap, Filter.map_comap_of_mem hr𝒰])
  -- `|Ψ|(|τ̂|(𝒱)) = |P|(𝒰) → |β| = |Ψ|(|o_β|)`
  have hτ𝒱 : Tendsto U.τ.orbitMap 𝒱 (𝓝 ((actionEpGroupoid U.Ψ.smooth_smul).π U.model.pt)) := by
    refine hΨe.isInducing.tendsto_nhds_iff.2 ?_
    have h1 : U.Ψ.functor.orbitMap ((actionEpGroupoid U.Ψ.smooth_smul).π U.model.pt) =
        B.toGroupoidStr.π β := by
      change B.toGroupoidStr.π (U.Ψ.obj U.model.pt) = _
      rw [U.obj_pt]
    rw [h1]
    have h2 : (U.Ψ.functor.orbitMap ∘ U.τ.orbitMap) = P.orbitMap ∘ U.hat.orbitMap :=
      funext fun c => (U.orbitMap_comm c).symm
    rw [h2, ← tendsto_map'_iff]
    change Tendsto P.orbitMap ((𝒱.map U.hat.orbitMap : Ultrafilter A.OrbitSpace) : Filter _) _
    rw [h𝒱]
    exact hz
  obtain ⟨c, hcτ, hc𝒱⟩ :=
    ((U.isProperCovering_τ hPc).isProperMap_orbitMap).ultrafilter_le_nhds_of_tendsto hτ𝒱
  refine ⟨U.hat.orbitMap c, ?_, ?_⟩
  · change P.orbitMap (U.hat.orbitMap c) ∈ K
    rw [U.orbitMap_comm, hcτ]
    refine ⟨β, hβ, ?_⟩
    change B.toGroupoidStr.π β = B.toGroupoidStr.π (U.Ψ.obj U.model.pt)
    rw [U.obj_pt]
  · rw [← h𝒱, Ultrafilter.coe_map]
    exact (hhe.continuous.tendsto c).mono_left (map_mono hc𝒱) |>.trans le_rfl

end ProperCoveringUniformizerConstruction

/-! ### Witness: `Θ₀ = 1_{0}` on `ℤˣ ⋉ ℝ` and the two sheets -/

section Witness

attribute [local instance] instMulActionUnitsBool'

open ProperCoveringUniformizerConstruction

/-- **Witness for Proposition 17.8.16 and its (4)**: for the two-sheet covering
`ℤˣ ⋉ (Bool × ℝ) → ℤˣ ⋉ ℝ` with its sheet construction and `Θ₀ = 1_{0}` (a branched
ep⁺-subcategory: `0` has isotropy `ℤ/2`), the hypotheses hold (`unif_hyp`: `F(0) ≠ ∅`), `Θ₀ ∘ P` is
branched with compact support, and it is `1` at the two objects `(true, 0)` and `(false, 0)`. -/
theorem proposition_17_8_16_reflection :
    (sheetConstruction isScSmoothMap_units_smul Bool).IsBranchedBase reflectionTheta ∧
      (∀ β, 0 < reflectionTheta β →
        ((sheetConstruction isScSmoothMap_units_smul Bool).F β).Nonempty) ∧
      (sheetConstruction isScSmoothMap_units_smul Bool).IsBranchedHat
        (reflectionTheta ∘ (sheetGCTFunctor isScSmoothMap_units_smul Bool).obj) ∧
      IsCompact ((sheetGCT isScSmoothMap_units_smul Bool).toGroupoidStr.π ''
        {α | 0 < reflectionTheta ((sheetGCTFunctor isScSmoothMap_units_smul Bool).obj α)}) ∧
      (reflectionTheta ∘ (sheetGCTFunctor isScSmoothMap_units_smul Bool).obj) (true, 0) = 1 ∧
      (reflectionTheta ∘ (sheetGCTFunctor isScSmoothMap_units_smul Bool).obj) (false, 0) = 1 := by
  have hPc := isProperCoveringGCT_sheet isScSmoothMap_units_smul
    (fun (_ : ℤˣ) (_ : Bool) => rfl)
  have hΘ := isBranchedEpSubgroupoid_reflectionTheta
  have hB : (sheetConstruction isScSmoothMap_units_smul Bool).IsBranchedBase reflectionTheta :=
    { nonneg := hΘ.nonneg
      isFunctorial := hΘ.isFunctorial
      isBranched := by
        rintro β _ ⟨h, rfl⟩
        exact hΘ }
  have unif_hyp : ∀ β, 0 < reflectionTheta β →
      ((sheetConstruction isScSmoothMap_units_smul Bool).F β).Nonempty := by
    intro β hβ
    have h0 : β = 0 := by
      by_contra h
      rw [reflectionTheta_apply, if_neg h] at hβ
      exact lt_irrefl _ hβ
    subst h0
    exact ⟨_, sheetUniformizer_mem isScSmoothMap_units_smul Bool 0 units_smul_zero_rn⟩
  refine ⟨hB, unif_hyp, proposition_17_8_16 hPc hB,
    proposition_17_8_16_four hPc hΘ.isFunctorial unif_hyp ?_,
    by simp [reflectionTheta_apply], by simp [reflectionTheta_apply]⟩
  have hs : {β : Fin 1 → ℝ | 0 < reflectionTheta β} = {0} := by
    ext β
    by_cases h : β = 0 <;> simp [reflectionTheta_apply, h]
  rw [hs, image_singleton]
  exact isCompact_singleton

end Witness

end Polyfold
