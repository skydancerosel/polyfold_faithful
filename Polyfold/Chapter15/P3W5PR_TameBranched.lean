import Polyfold.Chapter15.P3W3G_GeneralPosition
import Polyfold.Chapter11.GapP2_H4CrossChart

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 15,
§15.2 (pp. 688–690) and Remark 15.3.6 (p. 693): the local solution sets `Mᵢ` are **tame**
submanifolds and `Λ ∘ f` is a **tame** branched ep⁺-subgroupoid (Definition 9.3.6).

# Tame local branching structures of `Λ ∘ f`

## The text, paraphrased

(Remark 15.2.3) On `U(x)` the functor `z ↦ Λ(f(z))` is a tame branched ep⁺-subgroupoid.
(Theorem 15.2.5) At a point of good position there are a neighbourhood `U(x)` with the natural
`G_x`-action and tame submanifolds `Mᵢ` with weights `σᵢ` representing `Λ ∘ f`; `Λ ∘ f` is then a
tame branched ep⁺-subgroupoid.  (Remark 15.3.6) In general position `Λ ∘ f` is a tame branched
ep⁺-subgroupoid.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `exists_tame_solutionSet_of_isBranchGoodPosition`: a branch `f − s` in good position at `x`
  (Part I's Definition 3.6.6 on `W|O`) has an open `V ∋ x` with `{y ∈ V | f(y) = s(y)}` a smooth
  submanifold (Definition 4.2.1) **with a tame induced structure** (Definition 2.5.18): Part I's
  Theorem 3.1.26 on `W|O`, carried to `X` by the sc-diffeomorphism `O → X`.
* `isGoodPositionAt_of_interior`: at an interior point (`d_X(x) = 0`) transversality
  (Definition 15.2.1) is good position (Definition 15.2.4).
* **`theorem_15_2_5_tame_hyp`**: at a point of good position, `z ↦ Λ(f(z))` has a tame local
  branching structure (`TameBranchingStructure`, Definition 9.3.6): a natural representation
  `U(x)` with the properness property (Definition 7.5.8), the `Mᵢ = {z ∈ U(x) | f(z) = sᵢ(z)}` of
  the branches through `f(x)`, each with a tame induced structure.
* **`remark_15_2_3_tame_hyp`**: the same at an interior point of transversality.
* **`theorem_15_2_5_isTameBranched_hyp`**, **`remark_15_2_3_isTameBranched_hyp`**,
  **`remark_15_3_6_isTameBranched_hyp`**: the global forms: `Λ ∘ f` is a branched
  ep⁺-subgroupoid (Definition 9.1.2) and tame (`IsTameBranched`, Definition 9.3.6) under good
  position on the support, under transversality with `d_X = 0` on the support, and under general
  position (Definition 15.3.5).
* `theorem_15_3_7_in_particular_tame_hyp`: the "in particular" sentence of Theorem 15.3.7 with
  "tame": `Λ ∘ f` is a compact tame branched ep⁺-subgroupoid.

## Reading

* As in §15.2, `f` carries germ data in tame charts (`IsScFredholmSectionTame`), the inherited
  Part I hypothesis of Theorem 3.6.8; the global forms carry the paracompactness of
  `|supp(Λ ∘ f)|` (Definition 9.1.2 (1), new in 2021), as the earlier forms do.
* The `Mᵢ` are indexed by the branches through `f(x)` (the text's `I`, as in
  `remark_15_2_3_hyp`), so that each passes through `x`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid

variable {A : SEP.{u}}

/-! ### One branch: the tame local solution set -/

/-- **The local solution set of a branch in good position has a tame induced structure**
(Theorem 15.2.5, "tame submanifolds"): if `(f − s)|O` is in good position at `x` in a tame chart
(`IsBranchGoodPosition`), there is an open `V ∋ x` in `O` such that `{y ∈ V | f(y) = s(y)}` is a
smooth submanifold of `X` (Definition 4.2.1) whose induced structure is tame (Definition 2.5.18).
Part I's Theorem 3.1.26 (`theorem_3_1_26'`) on `W|O`, and the inclusion `O → X`. -/
theorem exists_tame_solutionSet_of_isBranchGoodPosition {f : A.Obj → A.W}
    (hft : A.B.IsScFredholmSectionTame f) {s : A.Obj → A.W} {O : Set A.Obj} (hO : IsOpen O)
    (hs : IsScPlusSectionOn A s O) {x : A.Obj} (hxO : x ∈ O) (hfs : f x = s x)
    (hgp : IsBranchGoodPosition f s hO x hxO) :
    ∃ V : Set A.Obj, IsOpen V ∧ x ∈ V ∧ V ⊆ O ∧
      A.X.PObj.IsSmoothSubmanifold {y ∈ V | f y = s y} ∧
      A.X.PObj.HasTameInducedStructure {y ∈ V | f y = s y} := by
  have : Nonempty O := ⟨⟨x, hxO⟩⟩
  have := A.X.PObj.paracompactSpace_subtype O
  have := paracompactSpace_pullbackSpace (f := (Subtype.val : O → A.Obj))
    (A.X.PObj.restrictOpen hO) A.B
  obtain ⟨_, hg⟩ := hgp
  have hf := hft.isScSmooth.1
  have hgO := isScFredholmSectionTame_subRestrict hO hft hs
  have hzero : ∀ y : O, IsZeroAt (pullbackProj A.P (Subtype.val : O → A.Obj))
      (subRestrict (O := O) f s hf) y ↔ f y.1 = s y.1 := fun y => by
    unfold subRestrict
    rw [isZeroAt_restrictSection_iff]
    exact isZeroAt_subSec_iff hf hs.1 y.2
  obtain ⟨U, hUo, hxU, hall, -, -, hsubM, htame, -⟩ :=
    theorem_3_1_26' hgO ((hzero ⟨x, hxO⟩).2 hfs) hg
  have eN : {y ∈ U | IsZeroAt (pullbackProj A.P (Subtype.val : O → A.Obj))
      (subRestrict (O := O) f s hf) y} =
      solutionSet (pullbackProj A.P (Subtype.val : O → A.Obj)) (subRestrict (O := O) f s hf) ∩
        U := by
    ext y; exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have hSm := StrongBundle.isSmoothSubmanifold_solutionSet_inter hgO.isScSmooth.1 hUo
    (fun y hy hy0 => hall y hy hy0)
  have hT : (A.X.PObj.restrictOpen hO).HasTameInducedStructure
      (solutionSet (pullbackProj A.P (Subtype.val : O → A.Obj)) (subRestrict (O := O) f s hf) ∩
        U) := by
    rw [← eN]; exact ⟨hsubM, htame⟩
  have hdiff := MPolyfold.isScDiffeoOn_subtypeVal (P := A.X.PObj) hO
  have himg := hSm.image_of_isScDiffeoOn hdiff (subset_univ _)
  have htimg := hT.image_of_isScDiffeoOn hSm hdiff (subset_univ _)
  have e : {y ∈ Subtype.val '' U | f y = s y} = Subtype.val ''
      (solutionSet (pullbackProj A.P (Subtype.val : O → A.Obj)) (subRestrict (O := O) f s hf) ∩
        U) := by
    ext y
    constructor
    · rintro ⟨⟨v, hvU, rfl⟩, hfy⟩; exact ⟨v, ⟨(hzero v).2 hfy, hvU⟩, rfl⟩
    · rintro ⟨v, ⟨hv0, hvU⟩, rfl⟩; exact ⟨⟨v, hvU, rfl⟩, (hzero v).1 hv0⟩
  refine ⟨Subtype.val '' U, hO.isOpenMap_subtype_val U hUo, ⟨⟨x, hxO⟩, hxU, rfl⟩,
    Subtype.coe_image_subset O U, ?_, ?_⟩
  · rw [e]; exact himg
  · rw [e]; exact htimg

/-! ### Interior points: transversality is good position -/

/-- **At an interior point, transversality is good position** (Definitions 15.2.1 and 15.2.4):
if `d_X(x) = 0` and `(f, Λ)` is transversal at `x`, every branch through `f(x)` of a local
sc⁺-section structure of `Λ` at `x` is in good position at `x` in a tame chart (Part I's
`isGoodPositionGerm_of_isLinSurjAt` on `W|O`). -/
theorem isGoodPositionAt_of_interior {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ)
    {x : A.Obj} (hd : A.X.PObj.degIndex x = 0) (htr : IsTransversalAt f Λ x) :
    IsGoodPositionAt f Λ x := by
  obtain ⟨hpos, hx1, hon⟩ := htr
  obtain ⟨R₀, k, s, σ, hrep⟩ := hΛ.2 x
  obtain ⟨c₀, hc₀, hxc₀⟩ := StrongBundle.exists_chart_mem A.B x
  have hso : IsOpen (c₀.φ.source ∩ R₀.U) := c₀.φ.isOpen_source.inter R₀.isOpen_U
  obtain ⟨c, hc, hcsrc⟩ : ∃ c : StrongBundleChart A.X.PObj A.P, A.B.IsChart c ∧
      c.φ.source = c₀.φ.source ∩ R₀.U :=
    ⟨_, (StrongBundle.isChart_of_mem A.B hc₀).restrict inter_subset_left hso, rfl⟩
  have hsub : c.φ.source ⊆ R₀.U := hcsrc ▸ inter_subset_right
  have hxc : x ∈ c.φ.source := hcsrc ▸ ⟨hxc₀, R₀.mem_U⟩
  let d : LocalLinData A Λ (A.X.PObj.levelMk 1 x hx1) :=
    ⟨R₀.U, R₀.isOpen_U, k, s, σ, hrep, c, hc, hsub, hxc⟩
  have hon' := (isOntoAtLevel_iff hf d).1 hon
  refine ⟨hpos, ⟨hx1, hon⟩, R₀.U, R₀.isOpen_U, R₀.mem_U, k, s, σ, hrep, fun i hi => ?_⟩
  have hch : ChartOnto c (subDeriv c f (s i) (levelLift c.φ 1 x)) (levelLift c.φ 1 x) :=
    (surjective_toIntr_subDeriv_iff hft.isScSmooth (hrep.2.1 i) hc hsub
      (x := A.X.PObj.levelMk 1 x hx1) hxc hi.symm).1 (hon' i hi)
  have : Nonempty R₀.U := ⟨⟨x, R₀.mem_U⟩⟩
  have := A.X.PObj.paracompactSpace_subtype R₀.U
  have := paracompactSpace_pullbackSpace (f := (Subtype.val : R₀.U → A.Obj))
    (A.X.PObj.restrictOpen R₀.isOpen_U) A.B
  have hgO := isScFredholmSectionTame_subRestrict R₀.isOpen_U hft (hrep.2.1 i)
  have h0 : IsZeroAt (pullbackProj A.P (Subtype.val : R₀.U → A.Obj))
      (subRestrict (O := R₀.U) f (s i) hft.isScSmooth.1) ⟨x, R₀.mem_U⟩ := by
    unfold subRestrict
    rw [isZeroAt_restrictSection_iff]
    exact (isZeroAt_subSec_iff hft.isScSmooth.1 (hrep.2.1 i).1 R₀.mem_U).2 hi.symm
  have hd' : (A.X.PObj.restrictOpen R₀.isOpen_U).degIndex ⟨x, R₀.mem_U⟩ = 0 := by
    rw [MPolyfold.degIndex_restrictOpen A.X.PObj R₀.isOpen_U]; exact hd
  exact ⟨hft.isScSmooth.1, StrongBundle.isGoodPositionGerm_of_isLinSurjAt hgO h0 hd'
    (isLinSurjAt_subRestrict R₀.isOpen_U hft (hrep.2.1 i) hc hsub hxc
      (A.X.PObj.toBase_levelLift c.isChart hxc hx1) hch)⟩

/-! ### The tame local branching structure -/

open Classical in
/-- **Theorem 15.2.5 (2017: Theorem 15.3), p. 690, "tame submanifolds" and "tame branched"**,
with the inherited tame-germ hypothesis `hft`: if `(f, Λ)` is in good position at `x`
(Definition 15.2.4), `z ↦ Λ(f(z))` has a tame local branching structure at `x` (Definition 9.3.6):
a natural representation `U(x)` of `G_x` with the properness property (Definition 7.5.8), the
submanifolds `Mᵢ = {z ∈ U(x) | f(z) = sᵢ(z)}` of the branches through `f(x)` with tame induced
structures (Definition 2.5.18), and the weights `σᵢ`. -/
theorem theorem_15_2_5_tame_hyp {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) {Λ : A.W → ℚ≥0} {x : A.Obj}
    (hgp : IsGoodPositionAt f Λ x) :
    Nonempty (A.X.TameBranchingStructure (fun z => (Λ (f z) : ℚ)) x) := by
  obtain ⟨-, -, O, hO, hxO, k, s, σ, hrep, hbr⟩ := hgp
  have hsec : IsSection A.P f := hf.1.1.1
  have hfc : Continuous f := continuousOn_univ.1 hft.isScSmooth.2.continuousOn
  have hV : ∀ i, ∃ V : Set A.Obj, IsOpen V ∧ x ∈ V ∧ V ⊆ O ∧
      (s i x = f x → A.X.PObj.IsSmoothSubmanifold {y ∈ V | f y = s i y} ∧
        A.X.PObj.HasTameInducedStructure {y ∈ V | f y = s i y}) ∧
      (s i x ≠ f x → ∀ y ∈ V, f y ≠ s i y) := by
    intro i
    by_cases h : s i x = f x
    · obtain ⟨V, hVo, hxV, hVO, hS, hT⟩ :=
        exists_tame_solutionSet_of_isBranchGoodPosition hft hO (hrep.2.1 i) hxO h.symm (hbr i h)
      exact ⟨V, hVo, hxV, hVO, fun _ => ⟨hS, hT⟩, fun h' => absurd h h'⟩
    · exact ⟨{y ∈ O | f y ≠ s i y}, isOpen_sep_ne hfc hO (hrep.2.1 i).continuousOn,
        ⟨hxO, fun e => h e.symm⟩, sep_subset _ _, fun h' => absurd h' h, fun _ y hy => hy.2⟩
  choose V hVo hxV hVO hVt hVn using hV
  obtain ⟨Q, hxQ, hQ⟩ := A.X.exists_hasPropernessProperty x
  have hWo : IsOpen (Q ∩ O ∩ ⋂ i, V i) :=
    (hQ.1.inter hO).inter (isOpen_iInter_of_finite hVo)
  obtain ⟨R, hRW⟩ := A.X.theorem_7_1_13 x hWo ⟨⟨hxQ, hxO⟩, mem_iInter.2 hxV⟩
  have hRQ : R.U ⊆ Q := fun y hy => (hRW hy).1.1
  have hRV : ∀ i, R.U ⊆ V i := fun i y hy => mem_iInter.1 (hRW hy).2 i
  have hRO : R.U ⊆ O := fun y hy => (hRW hy).1.2
  have hcount : ∀ z ∈ R.U, Λ (f z) = ∑ i with f z = s i z, σ i := fun z hz => by
    have h := hrep.2.2.2 (f z) (by rw [hsec z]; exact hRO hz)
    rw [hsec z] at h
    rw [h, Finset.sum_filter]
  have hI : ∀ i, ∀ z ∈ R.U, f z = s i z → s i x = f x := fun i z hz hfz => by
    by_contra h
    exact hVn i h z (hRV i hz) hfz
  have eM : ∀ i, {z ∈ R.U | f z = s i z} = {z ∈ V i | f z = s i z} ∩ R.U := fun i => by
    ext z
    constructor
    · rintro ⟨hz, he⟩; exact ⟨⟨hRV i hz, he⟩, hz⟩
    · rintro ⟨⟨-, he⟩, hz⟩; exact ⟨hz, he⟩
  have hS : ∀ j : ULift.{u} {i : Fin k // s i x = f x},
      A.X.PObj.IsSmoothSubmanifold {z ∈ R.U | f z = s j.down.1 z} := fun j => by
    rw [eM]; exact (hVt j.down.1 j.down.2).1.inter_isOpen R.isOpen_U
  have hT : ∀ j : ULift.{u} {i : Fin k // s i x = f x},
      A.X.PObj.HasTameInducedStructure {z ∈ R.U | f z = s j.down.1 z} := fun j => by
    rw [eM]
    exact (hVt j.down.1 j.down.2).2.inter_isOpen (hVt j.down.1 j.down.2).1 R.isOpen_U
  have hP : ∀ j : ULift.{u} {i : Fin k // s i x = f x},
      IsProperMap (inclusion (sep_subset R.U fun z => f z = s j.down.1 z)) := fun j => by
    rw [isProperMap_inclusion_iff]
    have hcs : ContinuousOn (s j.down.1) R.U := (hrep.2.1 j.down.1).continuousOn.mono hRO
    have h1 : Continuous fun p : R.U => f p := hfc.comp continuous_subtype_val
    have h2 : Continuous fun p : R.U => s j.down.1 p :=
      hcs.comp_continuous continuous_subtype_val fun p => p.2
    convert isClosed_eq h1 h2 using 1
    ext p
    simp
  let B : A.X.LocalBranchingStructure (fun z => (Λ (f z) : ℚ)) x :=
    EpGroupoid.LocalBranchingStructure.mk R.U R.isOpen_U R.mem_U
      (ULift.{u} {i : Fin k // s i x = f x}) (fun j => {z ∈ R.U | f z = s j.down.1 z})
      (fun j => sep_subset _ _) hS (fun j => ⟨R.mem_U, j.down.2.symm⟩) hP
      (fun j => (σ j.down.1 : ℚ)) (fun j => by exact_mod_cast hrep.1 j.down.1) (by
        intro z hz
        have e0 : ((Λ (f z) : ℚ≥0) : ℚ) = ∑ i, if f z = s i z then (σ i : ℚ) else 0 := by
          rw [hcount z hz, Finset.sum_filter]
          refine (map_sum NNRat.coeHom _ _).trans (Finset.sum_congr rfl fun i _ => ?_)
          split_ifs <;> rfl
        have e1 : (∑ i, if f z = s i z then (σ i : ℚ) else 0) =
            ∑ i with s i x = f x, (if f z = s i z then (σ i : ℚ) else 0) :=
          (Finset.sum_filter_of_ne fun i _ hne => hI i z hz (by
            by_contra h
            exact hne (if_neg h))).symm
        have e2 : (∑ i with s i x = f x, (if f z = s i z then (σ i : ℚ) else 0)) =
            ∑ a : {i // s i x = f x}, (if f z = s a.1 z then (σ a.1 : ℚ) else 0) :=
          Finset.sum_subtype _ (fun i => by simp) _
        have e3 : (∑ a : {i // s i x = f x}, (if f z = s a.1 z then (σ a.1 : ℚ) else 0)) =
            ∑ j : ULift.{u} {i // s i x = f x},
              (if f z = s j.down.1 z then (σ j.down.1 : ℚ) else 0) :=
          (Fintype.sum_equiv Equiv.ulift _ _ fun _ => rfl).symm
        refine e0.trans (e1.trans (e2.trans (e3.trans ?_)))
        simp only [Finset.sum_filter]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs with h1 h2 h2 <;> first | rfl | exact absurd ⟨hz, h1⟩ h2 | exact absurd h2.2 h1)
  exact ⟨{ toLocalBranchingStructure := B
           rep := R
           U_eq := rfl
           hasPropernessProperty :=
             ⟨R.isOpen_U, hQ.2.of_subset (closure_mono hRQ) isClosed_closure⟩
           hasTameInducedStructure := hT }⟩

/-- **Remark 15.2.3 (2017: Remark 15.2), p. 689, "tame"**, local part, with the inherited
tame-germ hypothesis: at a point `y` of `supp(Λ ∘ f)` with `d_X(y) = 0` where `(f, Λ)` is
transversal, `z ↦ Λ(f(z))` has a tame local branching structure (Definition 9.3.6) on a natural
representation `U(y)`. -/
theorem remark_15_2_3_tame_hyp {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ)
    {y : A.Obj} (hd : A.X.PObj.degIndex y = 0) (htr : IsTransversalAt f Λ y) :
    Nonempty (A.X.TameBranchingStructure (fun z => (Λ (f z) : ℚ)) y) :=
  theorem_15_2_5_tame_hyp hf hft (isGoodPositionAt_of_interior hf hft hΛ hd htr)

/-! ### The global forms -/

/-- **Theorem 15.2.5, closing sentence of its statement, global form**: if `(f, Λ)` is in good
position at every point of `supp(Λ ∘ f)` and `|supp(Λ ∘ f)|` is paracompact (Definition 9.1.2
(1), new in 2021), then `Λ ∘ f` is a branched ep⁺-subgroupoid (Definition 9.1.2) and tame
(Definition 9.3.6). -/
theorem theorem_15_2_5_isTameBranched_hyp {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ)
    (hgp : ∀ y, 0 < Λ (f y) → IsGoodPositionAt f Λ y)
    (hpar : ParacompactSpace (A.X.orbitSupp fun z => (Λ (f z) : ℚ))) :
    A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)) ∧
      A.X.IsTameBranched (fun z => (Λ (f z) : ℚ)) := by
  have htame : ∀ z ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)),
      Nonempty (A.X.TameBranchingStructure (fun z => (Λ (f z) : ℚ)) z) := fun z hz =>
    theorem_15_2_5_tame_hyp hf hft (hgp z (by exact_mod_cast hz))
  have hB : A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)) :=
    { nonneg := fun z => NNRat.coe_nonneg (Λ (f z))
      isFunctorial := isFunctorial_comp hf hΛ
      support_subset := fun z hz => mem_smoothSet_of_pos hft hΛ (by exact_mod_cast hz)
      paracompactSpace_orbitSupp := hpar
      localBranching := fun z hz =>
        (htame z hz).map TameBranchingStructure.toLocalBranchingStructure }
  exact ⟨hB, htame⟩

/-- **Remark 15.2.3 (2017: Remark 15.2), p. 689, global form with "tame"**: if `(f, Λ)` is
transversal (Definition 15.2.1 (1)), `d_X = 0` on `supp(Λ ∘ f)` and `|supp(Λ ∘ f)|` is
paracompact, then `Λ ∘ f` is a tame branched ep⁺-subgroupoid (Definitions 9.1.2, 9.3.6). -/
theorem remark_15_2_3_isTameBranched_hyp {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ) (htr : IsTransversal f Λ)
    (hd : ∀ y, 0 < Λ (f y) → A.X.PObj.degIndex y = 0)
    (hpar : ParacompactSpace (A.X.orbitSupp fun z => (Λ (f z) : ℚ))) :
    A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)) ∧
      A.X.IsTameBranched (fun z => (Λ (f z) : ℚ)) :=
  theorem_15_2_5_isTameBranched_hyp hf hft hΛ
    (fun y hy => isGoodPositionAt_of_interior hf hft hΛ (hd y hy) (htr y hy)) hpar

/-- **Remark 15.3.6 (2017: Remark 15.6), p. 693, last sentence, with "tame"**, with the
inherited tame-germ hypothesis: if `(f, Λ)` is in general position (Definition 15.3.5) and
`|supp(Λ ∘ f)|` is paracompact (Definition 9.1.2 (1)), then `Λ ∘ f` is a tame branched
ep⁺-subgroupoid (Definitions 9.1.2 and 9.3.6). -/
theorem remark_15_3_6_isTameBranched_hyp {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ) (hgp : IsInGeneralPosition A f Λ)
    (hpar : ParacompactSpace (A.X.orbitSupp fun z => (Λ (f z) : ℚ))) :
    A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)) ∧
      A.X.IsTameBranched (fun z => (Λ (f z) : ℚ)) :=
  theorem_15_2_5_isTameBranched_hyp hf hft hΛ
    (fun _ hy => (remark_15_3_6_goodPosition_hyp hf hft hΛ hgp hy).1) hpar

/-- **Theorem 15.3.7, "In particular" (p. 694), with "tame"**, with the inherited tame-germ
hypothesis: if `Λ` is an sc⁺-multisection with `N(Λ) ≤ 1`, `dom-supp(Λ) ⊆ U`, `(f, Λ)` in
general position, and `(N, U)` controls compactness, then `Λ ∘ f` is a compact tame branched
ep⁺-subgroupoid (Definitions 9.1.2, 9.1.6 (2), 9.3.6). -/
theorem theorem_15_3_7_in_particular_tame_hyp {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {N : A.B.One → ℝ} {U : Set A.Obj} (hcc : ControlsCompactness A f N U) {Λ : A.W → ℚ≥0}
    (hΛ : IsScPlusMultisection A Λ) (hN1 : ∀ x, pointwiseNorm N Λ x ≤ 1)
    (hdom : domSupp Λ ⊆ U) (hgp : IsInGeneralPosition A f Λ) :
    A.X.IsBranchedEpSubgroupoid (fun z => (Λ (f z) : ℚ)) ∧
      A.X.IsCompactBranched (fun z => (Λ (f z) : ℚ)) ∧
      A.X.IsTameBranched (fun z => (Λ (f z) : ℚ)) := by
  obtain ⟨hB, hK⟩ := theorem_15_3_7_in_particular_hyp hf hft hcc hΛ hN1 hdom hgp
  exact ⟨hB, hK, (remark_15_3_6_isTameBranched_hyp hf hft hΛ hgp hB.paracompactSpace_orbitSupp).2⟩

end SBLocalization

end Polyfold
