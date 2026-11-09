import Polyfold.Chapter5.Homotopy
import Polyfold.Chapter3.NonVacuityG
import Polyfold.Chapter3.IndexAlongPaths

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 5, "The Fredholm
Package for M-Polyfolds": the statements that the 2021 edition changes, **Definition 5.2.1**
(p. 209; 2017: Definition 5.5; preprint: Definition 5.4), **Theorem 5.2.2** (p. 210; 2017:
Theorem 5.1; preprint: Theorem 5.5), **Theorem 5.3.5** (p. 217; 2017: Theorem 5.5; preprint:
Theorem 5.13) and **Definition 5.3.13** (p. 223; 2017: Definition 5.10; preprint:
Definition 5.20), with **Lemma 5.3.16** (p. 224; 2017: Lemma 5.4; preprint: Lemma 5.23) read
under the new Definition 5.3.13.  Chapter 5 has no item that is new in the 2021 edition.

# Chapter 5 in the 2021 edition

## The text, paraphrased

(Definition 5.2.1, p. 209) For an sc-smooth section `f` of a strong bundle: (1) `f` has a compact
solution set if `f⁻¹(0)` is compact; (2) `f` is weakly proper if, besides, for every auxiliary norm
`N` there is an open `U ⊇ f⁻¹(0)` such that for every sc⁺-section `s` supported in `U` with
`N(s(y)) ≤ 1` **for `y ∈ U`** the set `{f = s}` is compact; (3) proper: the closure of
`{x ∈ U | N(f(x)) ≤ 1}` is compact; (4) weakly proper`<∞` (new): as (2) with `sup_U N(s) < ∞`;
(5) proper`<∞` (new): as (3) for every constant `0 < C < ∞` in place of `1`.  (Theorem 5.2.2,
p. 210) For an sc-Fredholm section a compact solution set gives proper`<∞`; so the five properties
are equivalent.

(Theorem 5.3.5, p. 217) Over `X` with `∂X = ∅` admitting sc-smooth bump functions, for `f`
sc-Fredholm with compact solution set and `N` an auxiliary norm, there is an open `U ⊇ f⁻¹(0)`
such that `S_{f+s}` is compact for sc⁺-sections `s` supported in `U` with `N ≤ 1`, and a dense
set of such `s` for which `f + s` is transversal; then `S_{f+s}` is a **compact** sub-M-polyfold
whose induced structure is that of a compact manifold without boundary.

(Definition 5.3.13, p. 223) A generalized compact homotopy between compact sc-Fredholm problems
`(fᵢ, Pᵢ)`, `i = 0, 1`, is a tame strong bundle `P : Y → X`, an sc-Fredholm section `f` of `P`
with compact solution set and an sc-smooth `t : X → [0, 1]` with (1) `t⁻¹(i) = Xᵢ`, (2)
`(f|Xᵢ, P|Yᵢ) = (fᵢ, Pᵢ)`, (3) `dt : T_xX → ℝ` onto at every smooth `x`.  (Lemma 5.3.16, p. 224)
For a one-dimensional `Z` with `T_xX = Z ⊕ ker dt(x)` and `τ ∈ T*_xS` there is a unique `b_τ`
with values in `Z` and `dt(x) ∘ b_τ = τ`; adding an operator with values in `ker dt(x)` keeps this.

## What is formalized

* `StrongBundle.IsWeaklyProperOnU` (Definition 5.2.1 (2), bound on `U` only),
  `StrongBundle.IsWeaklyProperLtInfty` ((4)), `StrongBundle.IsProperLtInfty` ((5)); (1) and (3)
  are the existing `IsCompact (solutionSet P f)` and `StrongBundle.IsProper`.
  `isWeaklyProperOnU_iff`: the 2021 form of (2) is equivalent to the existing
  `StrongBundle.IsWeaklyProper` (bound everywhere), since `s` vanishes off `U`.
* The a priori implications of p. 209: `IsProperLtInfty.isProper`,
  `IsWeaklyProperLtInfty.isWeaklyProperOnU`, `IsProper.isWeaklyProperOnU`,
  `IsProperLtInfty.isWeaklyProperLtInfty`, `IsWeaklyProperOnU.isCompact_solutionSet`.
* `theorem_5_2_2` (compact solution set ⟹ proper`<∞`) and `theorem_5_2_2_tfae` (the
  five properties are equivalent), by the argument of `theorem_5_2_2_preprint` with bounds `A·C`.
* `theorem_5_3_5`: `theorem_5_3_5_preprint` with the conclusion that `S_{f+s}` is a sub-M-polyfold and
  compact (`isSubMPolyfold_solutionSet_of_manifold`; the empty set is a sub-M-polyfold).
* `MPolyfold.HasSurjDerivAt` (Definition 5.3.13 (3) in a chart), `IsCompactFredholmRestriction`
  (Definition 5.3.13 (2): `f` restricts to a tame sc-Fredholm section over the tame
  sub-M-polyfold `A`) and `StrongBundle.IsSubmersiveGenCompactHomotopy` (Definition 5.3.13).
* Relation to the existing reading of the 2014/2017 definition (`IsGenCompactHomotopy`):
  `IsGenCompactHomotopy.isSubmersiveGenCompactHomotopy` (the old data plus (3) give the new);
  `not_isGenCompactHomotopy_witness` (the converse fails); the dependent result
  `IsSubmersiveGenCompactHomotopy.isCompact_solutionSet_restrict` (every fibre `t⁻¹(τ)` has a
  compact solution set) is re-derived from the new data.
* `lemma_5_3_16`: under (3), `dt(x) ≠ 0` on the tangent space `T_zO` of a chart, a
  one-dimensional complement `Z` of its kernel exists, and Lemma 5.3.16 holds (`lemma_5_3_16_preprint`).
  This supplies the hidden hypothesis `dt(x) ≠ 0` of the existing Lemma 5.3.16 (preprint 5.23) (gap G.48).
* Satisfiability (`isSubmersiveGenCompactHomotopy_witness`): on `ℝ` with the graph section of
  `id` and `t(x) = 1/2 + arctan(x)/π`, all of Definition 5.3.13 holds (the ends are empty).

## What the text leaves implicit, and the choices made

* In Theorem 5.3.5 the bound is printed `N(f(x)) ≤ 1`; we read it as `N(s(x)) ≤ 1` (possible
  misprint; the proof and the 2017 text bound `s`), which is `allowableSections` of
  `theorem_5_3_5_preprint`.
* `t : X → [0, 1]` is read as `t x ∈ [0, 1]` (`mem_Icc`); 2021 drops the surjectivity of `t` and
  the requirement that every fibre `X_τ` be a tame sc-Fredholm problem.  (1)–(2) are read as: for
  `i ∈ {0, 1}`, `t⁻¹(i)` is a tame sub-M-polyfold over which `f` restricts to a tame sc-Fredholm
  section; the problems `(fᵢ, Pᵢ)` are those restrictions (Remark 5.3.14 allows isomorphic ones).
* `dt(x)` is read in a chart `φ` around `x` with a retraction `R` of the model onto `O`: on
  `T_zO = R'(z)(E₀)` the derivative of `t ∘ φ⁻¹ ∘ R` is onto `ℝ`, as for the project's
  `IsLinSurjAt`; tangent spaces carry no linear structure of their own in the project.
* With the new data the end fibres may be empty (as in the witness), and the fibres `X_τ`,
  `0 < τ < 1`, need not be sub-M-polyfolds; the fibre statement of the old definition is the
  hypothesis that 2021 replaces by (3).
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Function
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

section Def521

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

namespace StrongBundle

variable (B) in
/-- **2021 Definition 5.2.1 (2), p. 209** (2017: Definition 5.5 (2); preprint: Definition 5.4):
`f` is **weakly proper**: its solution set is compact, and for every auxiliary norm `N` there is an
open `U ⊇ f⁻¹(0)` such that `{f = s}` is compact for every sc⁺-section `s` supported in `U` with
`N(s(y)) ≤ 1` for `y ∈ U` (2021 bounds `s` on `U` only). -/
def IsWeaklyProperOnU (f : X → Y) : Prop :=
  IsCompact (solutionSet P f) ∧ ∀ N : B.One → ℝ, B.IsAuxNorm N → ∃ U : Set X, IsOpen U ∧
    solutionSet P f ⊆ U ∧ ∀ s : X → Y, B.IsScPlusSection s → closure {x | ¬ IsZeroAt P s x} ⊆ U →
      (∀ y ∈ U, B.AuxLe N (s y) 1) → IsCompact {x | f x = s x}

variable (B) in
/-- **2021 Definition 5.2.1 (4), p. 209** (new in the 2021 edition): `f` is **weakly
proper`<∞`**: as weakly proper, for every sc⁺-section `s` supported in `U` with
`sup_{y ∈ U} N(s(y)) < ∞`. -/
def IsWeaklyProperLtInfty (f : X → Y) : Prop :=
  IsCompact (solutionSet P f) ∧ ∀ N : B.One → ℝ, B.IsAuxNorm N → ∃ U : Set X, IsOpen U ∧
    solutionSet P f ⊆ U ∧ ∀ s : X → Y, B.IsScPlusSection s → closure {x | ¬ IsZeroAt P s x} ⊆ U →
      (∃ C : ℝ, ∀ y ∈ U, B.AuxLe N (s y) C) → IsCompact {x | f x = s x}

variable (B) in
/-- **2021 Definition 5.2.1 (5), p. 209** (new in the 2021 edition): `f` is **proper`<∞`**:
compact solution set, and for every auxiliary norm `N` an open `U ⊇ f⁻¹(0)` such that the closure
of `{x ∈ U | N(f(x)) ≤ C}` is compact for every constant `0 < C < ∞` (with `N = ∞` off `Y_{0,1}`,
`AuxLe`). -/
def IsProperLtInfty (f : X → Y) : Prop :=
  IsCompact (solutionSet P f) ∧ ∀ N : B.One → ℝ, B.IsAuxNorm N → ∃ U : Set X, IsOpen U ∧
    solutionSet P f ⊆ U ∧ ∀ C : ℝ, 0 < C → IsCompact (closure {x ∈ U | B.AuxLe N (f x) C})

/-- The zero of a fibre satisfies `N ≤ r` for every `r ≥ 0`. -/
lemma IsAuxNorm.auxLe_fiberZero {N : B.One → ℝ} (hN : B.IsAuxNorm N) (x : X) {r : ℝ}
    (hr : 0 ≤ r) : B.AuxLe N (fiberZero P x) r := by
  refine ⟨B.fiberZero_mem_oneSet x, ?_⟩
  have e : B.oneMk (fiberZero P x) (B.fiberZero_mem_oneSet x) = B.zeroOne x :=
    B.oneVal_injective (by rw [oneVal_oneMk, oneVal_zeroOne])
  rw [e, (hN.fiber x).map_zero]
  exact hr

/-- The bound `N(y) ≤ r` is monotone in `r`. -/
lemma AuxLe.mono {N : B.One → ℝ} {y : Y} {r r' : ℝ} (h : B.AuxLe N y r) (hrr' : r ≤ r') :
    B.AuxLe N y r' := ⟨h.1, h.2.trans hrr'⟩

omit [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
  [∀ x, Module ℝ (P ⁻¹' {x})] in
/-- A section supported in `U` vanishes off `U`. -/
lemma isZeroAt_of_not_mem_of_support_subset {s : X → Y} {U : Set X}
    (hsupp : closure {x | ¬ IsZeroAt P s x} ⊆ U) {x : X} (hx : x ∉ U) : IsZeroAt P s x := by
  by_contra hnz
  exact hx (hsupp (subset_closure hnz))

/-- The 2021 form of Definition 5.2.1 (2) (`N(s) ≤ 1` on `U`) is equivalent to the existing
`IsWeaklyProper` (`N(s) ≤ 1` everywhere, 2017/preprint), since `s` vanishes off `U`. -/
theorem isWeaklyProperOnU_iff :
    B.IsWeaklyProperOnU f ↔ B.IsWeaklyProper f := by
  constructor
  · rintro ⟨hS, h⟩
    refine ⟨hS, fun N hN => ?_⟩
    obtain ⟨U, hUo, hSU, hU⟩ := h N hN
    exact ⟨U, hUo, hSU, fun s hs hsupp hsN => hU s hs hsupp fun y _ => hsN y⟩
  · rintro ⟨hS, h⟩
    refine ⟨hS, fun N hN => ?_⟩
    obtain ⟨U, hUo, hSU, hU⟩ := h N hN
    refine ⟨U, hUo, hSU, fun s hs hsupp hsN => hU s hs hsupp fun y => ?_⟩
    by_cases hy : y ∈ U
    · exact hsN y hy
    · have hz := isZeroAt_of_not_mem_of_support_subset hsupp hy
      exact (hN.auxLe_fiberZero y zero_le_one).congr hz.symm

/-- p. 209: proper`<∞` implies proper (take `C = 1`). -/
theorem IsProperLtInfty.isProper (h : B.IsProperLtInfty f) : B.IsProper f := by
  refine ⟨h.1, fun N hN => ?_⟩
  obtain ⟨U, hUo, hSU, hK⟩ := h.2 N hN
  exact ⟨U, hUo, hSU, hK 1 one_pos⟩

/-- p. 209: weakly proper`<∞` implies weakly proper (the bound `1` is finite). -/
theorem IsWeaklyProperLtInfty.isWeaklyProperOnU (h : B.IsWeaklyProperLtInfty f) :
    B.IsWeaklyProperOnU f := by
  refine ⟨h.1, fun N hN => ?_⟩
  obtain ⟨U, hUo, hSU, hK⟩ := h.2 N hN
  exact ⟨U, hUo, hSU, fun s hs hsupp hsN => hK s hs hsupp ⟨1, hsN⟩⟩

/-- p. 209: proper implies weakly proper (`IsProper.isWeaklyProper`). -/
theorem IsProper.isWeaklyProperOnU (hfc : Continuous f) (h : B.IsProper f) :
    B.IsWeaklyProperOnU f :=
  isWeaklyProperOnU_iff.2 (h.isWeaklyProper hfc)

/-- p. 209: proper`<∞` implies weakly proper`<∞`: a solution of `f = s` lies in `U` and has
`N(f(x)) = N(s(x)) ≤ C`. -/
theorem IsProperLtInfty.isWeaklyProperLtInfty (hfc : Continuous f) (h : B.IsProperLtInfty f) :
    B.IsWeaklyProperLtInfty f := by
  refine ⟨h.1, fun N hN => ?_⟩
  obtain ⟨U, hUo, hSU, hK⟩ := h.2 N hN
  refine ⟨U, hUo, hSU, fun s hs hsupp ⟨C, hsC⟩ => ?_⟩
  have hsc : Continuous s := continuous_iff_continuousAt.2 fun x => by
    obtain ⟨c, hc, hx⟩ := B.exists_chart_mem x
    exact (hs.continuousOn_source (B.isChart_of_mem hc)).continuousAt
      (c.φ.isOpen_source.mem_nhds hx)
  refine (hK (max C 1) (lt_of_lt_of_le one_pos (le_max_right _ _))).of_isClosed_subset
    (isClosed_eq hfc hsc) fun x hx => subset_closure ⟨?_, ?_⟩
  · by_contra hxU
    have hz := isZeroAt_of_not_mem_of_support_subset hsupp hxU
    exact hxU (hSU (show IsZeroAt P f x from (show f x = s x from hx).trans hz))
  · have hxU : x ∈ U := by
      by_contra hxU
      have hz := isZeroAt_of_not_mem_of_support_subset hsupp hxU
      exact hxU (hSU (show IsZeroAt P f x from (show f x = s x from hx).trans hz))
    exact ((hsC x hxU).mono (le_max_left _ _)).congr (show f x = s x from hx).symm

/-- p. 209: weakly proper implies a compact solution set. -/
theorem IsWeaklyProperOnU.isCompact_solutionSet (h : B.IsWeaklyProperOnU f) :
    IsCompact (solutionSet P f) := h.1

end StrongBundle

open StrongBundle

/-- **2021 Theorem 5.2.2, p. 210** (2017: Theorem 5.1; preprint: Theorem 5.5), first sentence:
an sc-Fredholm section with a compact solution set is proper`<∞`.  The proof is that of
`theorem_5_2_2_preprint`: near each zero the closure of `{N(f) ≤ C}` lies in a compact set given by the
contraction germ, for the bound `A · C`; the neighbourhood does not depend on `C`. -/
theorem theorem_5_2_2 (hf : B.IsScFredholmSection f) (hS : IsCompact (solutionSet P f)) :
    B.IsProperLtInfty f := by
  refine ⟨hS, fun N hN => ?_⟩
  have hsec := hf.isScSmooth.1
  have hloc : ∀ x ∈ solutionSet P f, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∀ C : ℝ, 0 < C → IsCompact (closure {y ∈ V | B.AuxLe N (f y) C}) := by
    intro x hx
    obtain ⟨c, hc, hxc, V, hVo, hxV, hVc, hK⟩ :=
      exists_nbhd_isCompact_closure_bdd (hf.germ x (hf.mem_smoothSet_of_isZeroAt hx))
    obtain ⟨V₁, hV₁o, hxV₁, -, A, hA, hV₁⟩ := hN.exists_norm_liftOne_le hc hxc
    refine ⟨V ∩ V₁, hVo.inter hV₁o, ⟨hxV, hxV₁⟩, fun C hC =>
      (hK (A * C)).of_isClosed_subset isClosed_closure (closure_mono ?_)⟩
    rintro y ⟨⟨hyV, hyV₁⟩, hy1, hyN⟩
    refine ⟨hyV, (c.liftOne (f y)).2, ?_, ?_⟩
    · exact toBase_liftOne_snd hc (c.mem_source_of_proj (by rw [hsec y]; exact hVc hyV)) hy1
    · have := hV₁ (B.oneMk (f y) hy1) (by rw [oneVal_oneMk, hsec y]; exact hyV₁)
      rw [oneVal_oneMk] at this
      calc ‖(c.liftOne (f y)).2‖ ≤ A * N (B.oneMk (f y) hy1) := this
        _ ≤ A * C := mul_le_mul_of_nonneg_left hyN hA.le
  choose! V hVo hxV hVK using hloc
  obtain ⟨t, htS, hcover⟩ := hS.elim_nhds_subcover V fun x hx => (hVo x hx).mem_nhds (hxV x hx)
  refine ⟨⋃ x ∈ t, V x, isOpen_biUnion fun x hx => hVo x (htS x hx), hcover, fun C hC => ?_⟩
  have hK : IsCompact (⋃ x ∈ t, closure {y ∈ V x | B.AuxLe N (f y) C}) :=
    t.isCompact_biUnion fun x hx => hVK x (htS x hx) C hC
  refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)
  rintro y ⟨hyU, hyN⟩
  obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 hyU
  exact mem_iUnion₂.2 ⟨x, hx, subset_closure ⟨hyx, hyN⟩⟩

/-- **2021 Theorem 5.2.2, p. 210**, second sentence: for an sc-Fredholm section, a compact
solution set, weakly proper, proper, weakly proper`<∞` and proper`<∞` are equivalent. -/
theorem theorem_5_2_2_tfae (hf : B.IsScFredholmSection f) :
    List.TFAE [IsCompact (solutionSet P f), B.IsWeaklyProperOnU f, B.IsProper f,
      B.IsWeaklyProperLtInfty f, B.IsProperLtInfty f] := by
  have hfc : Continuous f := continuousOn_univ.1 hf.isScSmooth.2.continuousOn
  tfae_have 5 → 3 := IsProperLtInfty.isProper
  tfae_have 3 → 2 := IsProper.isWeaklyProperOnU hfc
  tfae_have 2 → 1 := IsWeaklyProperOnU.isCompact_solutionSet
  tfae_have 1 → 5 := theorem_5_2_2 hf
  tfae_have 5 → 4 := IsProperLtInfty.isWeaklyProperLtInfty hfc
  tfae_have 4 → 2 := IsWeaklyProperLtInfty.isWeaklyProperOnU
  tfae_finish

end Def521

section Theorem535

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

/-- A solution set that is a manifold whenever it is non-empty is a sub-M-polyfold (the empty set
is one). -/
theorem isSubMPolyfold_solutionSet_of_manifold {h : X → Y}
    (hm : (solutionSet P h).Nonempty → B.SolutionSetIsManifold h) :
    PX.IsSubMPolyfold (solutionSet P h) := by
  rcases (solutionSet P h).eq_empty_or_nonempty with he | hne
  · rw [he]; intro a ha; exact absurd ha (notMem_empty a)
  · exact (hm hne).1

/-- **2021 Theorem 5.3.5, p. 217** (2017: Theorem 5.5; preprint: Theorem 5.13): the conclusions
of `theorem_5_3_5_preprint`, with the 2021 addition that for the transversal perturbations `S_{f+s}` is a
**compact sub-M-polyfold** (and a manifold when non-empty).  The perturbations are the
`allowableSections` (support in `U`, `N(s) ≤ 1`); the printed `N(f(x)) ≤ 1` is read as
`N(s(x)) ≤ 1` (possible misprint). -/
theorem theorem_5_3_5 (hX : PX.IsWithoutBoundary) (hbump : PX.AdmitsBumpFunctions)
    {f : X → Y} (hf : B.IsScFredholmSectionTame f) (hS : IsCompact (solutionSet P f))
    {N : B.One → ℝ} (hN : B.IsAuxNorm N) :
    ∃ U : Set X, IsOpen U ∧ solutionSet P f ⊆ U ∧
      (∀ s ∈ B.allowableSections N U, IsCompact (solutionSet P (sectionAdd P f s))) ∧
      ∀ (s' : X → Y) (hs' : B.IsScPlusSection s'), s' ∈ B.allowableSections N U → ∀ ε > 0,
        ∃ (s : X → Y) (hs : B.IsScPlusSection s), s ∈ B.allowableSections N U ∧
          (∀ x, B.sectionDistAt N hs hs' x ≤ ε) ∧
          B.IsTransversal (sectionAdd P f s) ∧
          (PX.IsSubMPolyfold (solutionSet P (sectionAdd P f s)) ∧
            IsCompact (solutionSet P (sectionAdd P f s))) ∧
          ((solutionSet P (sectionAdd P f s)).Nonempty →
            B.SolutionSetIsManifold (sectionAdd P f s)) := by
  obtain ⟨U, hUo, hSU, hcpt, hdense⟩ := theorem_5_3_5_preprint hX hbump hf hS hN
  refine ⟨U, hUo, hSU, hcpt, fun s' hs' hs'a ε hε => ?_⟩
  obtain ⟨s, hs, hsa, hdist, htr, hc, hm⟩ := hdense s' hs' hs'a ε hε
  exact ⟨s, hs, hsa, hdist, htr, ⟨isSubMPolyfold_solutionSet_of_manifold hm, hc⟩, hm⟩

end Theorem535

section Def5313

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

variable (PX) in
/-- **2021 Definition 5.3.13 (3), p. 223**, at a point: `dt(x) : T_xX → ℝ` is onto, read in a
chart `φ` around `x` with a retraction `R` onto the model `O` and a level-`1` lift `z` of `φ(x)`:
every `a ∈ ℝ` is `D(t ∘ φ⁻¹ ∘ R)(z)` of a tangent vector `R'(z) v ∈ T_zO`. -/
def MPolyfold.HasSurjDerivAt (t : X → ℝ) (x : X) : Prop :=
  ∃ (φ : MChart X) (_ : PX.IsChart φ) (_ : x ∈ φ.source)
    (R : ScRetraction φ.model.E φ.model.C) (_ : R.retract = φ.model.O) (z : φ.model.E 1),
    φ.model.E.toBase 1 z = φ x ∧
      ∀ a : ℝ, ∃ v : φ.model.E 0,
        scDeriv (F := ScBanach.const ℝ) R.U ((t ∘ φ.symm) ∘ R) z (scDeriv R.U R z v) = a

variable (B : StrongBundle PX P)

/-- **2021 Definition 5.3.13 (1)–(2), p. 223**, for one end `A = t⁻¹(i)`: `A` is a tame
sub-M-polyfold and `f` restricts to a tame sc-Fredholm section of the pulled back bundle (the
problem `(fᵢ, Pᵢ)`; this is the fibre clause of the existing `IsGenCompactHomotopy`). -/
def StrongBundle.IsCompactFredholmRestriction (f : X → Y) (hf : IsSection P f) (A : Set X) :
    Prop :=
  ∃ hsub : PX.IsSubMPolyfold A,
    haveI := PX.paracompactSpace_subtype A
    (MPolyfold.subPolyfold hsub).IsTame ∧
    haveI := paracompactSpace_pullbackSpace (f := (Subtype.val : A → X))
      (MPolyfold.subPolyfold hsub) B
    (B.pullback (MPolyfold.subPolyfold_inclusion_isScSmooth hsub)).IsScFredholmSectionTame
      (restrictSection P A f hf)

/-- **2021 Definition 5.3.13, p. 223** (2017: Definition 5.10; preprint: Definition 5.20):
a **generalized compact homotopy**: `X` tame, `f` a tame sc-Fredholm section with compact
solution set, `t : X → [0, 1]` sc-smooth, the ends `t⁻¹(0)`, `t⁻¹(1)` tame sc-Fredholm problems,
and `dt(x)` onto at every smooth `x`.  (The 2014/2017 reading, `IsGenCompactHomotopy`, asks `t`
onto `[0, 1]` and every fibre `t⁻¹(τ)` a tame sc-Fredholm problem, and has no condition (3).) -/
structure StrongBundle.IsSubmersiveGenCompactHomotopy (f : X → Y) (t : X → ℝ) : Prop where
  isTame : PX.IsTame
  isScFredholm : B.IsScFredholmSectionTame f
  isCompact : IsCompact (solutionSet P f)
  isScSmooth_t : PX.IsScSmoothMap realPolyfold t
  mem_Icc : ∀ x, t x ∈ Icc (0 : ℝ) 1
  ends : ∀ i ∈ ({0, 1} : Set ℝ),
    B.IsCompactFredholmRestriction f isScFredholm.isScSmooth.1 (t ⁻¹' {i})
  surjDeriv : ∀ x ∈ PX.smoothSet, PX.HasSurjDerivAt t x

variable {B}

/-- The 2014/2017 data together with 2021 Definition 5.3.13 (3) give the 2021 data. -/
theorem StrongBundle.IsGenCompactHomotopy.isSubmersiveGenCompactHomotopy {f : X → Y}
    {t : X → ℝ} (h : B.IsGenCompactHomotopy f t)
    (hdt : ∀ x ∈ PX.smoothSet, PX.HasSurjDerivAt t x) :
    B.IsSubmersiveGenCompactHomotopy f t where
  isTame := h.isTame
  isScFredholm := h.isScFredholm
  isCompact := h.isCompact
  isScSmooth_t := h.isScSmooth_t
  mem_Icc x := h.range_t ▸ mem_range_self x
  ends i hi := h.fibre i (by rcases hi with rfl | rfl <;> simp)
  surjDeriv := hdt

/-- Re-derived from the 2021 data: the restriction of `f` to every fibre `t⁻¹(τ)` has a compact
solution set (`t⁻¹(τ)` is closed and `f⁻¹(0)` compact); for `τ = 0, 1` these are the compact
problems `(fᵢ, Pᵢ)` of Definition 5.3.13. -/
theorem StrongBundle.IsSubmersiveGenCompactHomotopy.isCompact_solutionSet_restrict
    {f : X → Y} {t : X → ℝ} (h : B.IsSubmersiveGenCompactHomotopy f t) (τ : ℝ) :
    IsCompact (solutionSet (pullbackProj P (Subtype.val : t ⁻¹' {τ} → X))
      (restrictSection P (t ⁻¹' {τ}) f h.isScFredholm.isScSmooth.1)) := by
  have hcont : Continuous t := continuousOn_univ.1 h.isScSmooth_t.continuousOn
  have hcl : IsClosed (t ⁻¹' {τ}) := isClosed_singleton.preimage hcont
  have heq : solutionSet (pullbackProj P (Subtype.val : t ⁻¹' {τ} → X))
      (restrictSection P (t ⁻¹' {τ}) f h.isScFredholm.isScSmooth.1) =
      Subtype.val ⁻¹' solutionSet P f := by
    ext a
    exact isZeroAt_restrictSection_iff h.isScFredholm.isScSmooth.1 a
  rw [heq]
  exact hcl.isClosedEmbedding_subtypeVal.isCompact_preimage h.isCompact

end Def5313

section Lemma5316

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}

/-- **2021 Lemma 5.3.16, p. 224** (2017: Lemma 5.4; preprint: Lemma 5.23), under 2021
Definition 5.3.13 (3).  If `dt(x)` is onto (`HasSurjDerivAt`), then in a chart around `x` the
derivative `ℓ` of `t` on the tangent space `T_zO = R'(z)(E₀)` is non-zero (the hidden hypothesis
of `lemma_5_3_16_preprint`), `ker ℓ` has a one-dimensional complement `Z`, and for every linear `τ : S → ℝ`
there is a unique `b_τ : S → Z` with `ℓ ∘ b_τ = τ`; adding a map with values in `ker ℓ` keeps
`ℓ ∘ (b + a) = τ`. -/
theorem lemma_5_3_16 {t : X → ℝ} {x : X} (h : PX.HasSurjDerivAt t x) :
    ∃ (φ : MChart X) (_ : PX.IsChart φ) (_ : x ∈ φ.source)
      (R : ScRetraction φ.model.E φ.model.C) (_ : R.retract = φ.model.O) (z : φ.model.E 1)
      (_ : φ.model.E.toBase 1 z = φ x)
      (ℓ : LinearMap.range (scDeriv R.U R z : φ.model.E 0 →ₗ[ℝ] φ.model.E 0) →ₗ[ℝ] ℝ),
      ℓ = (scDeriv (F := ScBanach.const ℝ) R.U ((t ∘ φ.symm) ∘ R) z : φ.model.E 0 →ₗ[ℝ] ℝ) ∘ₗ
          (LinearMap.range (scDeriv R.U R z : φ.model.E 0 →ₗ[ℝ] φ.model.E 0)).subtype ∧
      ℓ ≠ 0 ∧
      ∃ Z : Submodule ℝ (LinearMap.range (scDeriv R.U R z : φ.model.E 0 →ₗ[ℝ] φ.model.E 0)),
        Module.finrank ℝ Z = 1 ∧ IsCompl Z (LinearMap.ker ℓ) ∧
        ∀ (S : Type) [AddCommGroup S] [Module ℝ S] (τ : S →ₗ[ℝ] ℝ),
          (∃! b : S →ₗ[ℝ] Z, ℓ ∘ₗ Z.subtype ∘ₗ b = τ) ∧
          ∀ b a : S →ₗ[ℝ] LinearMap.range (scDeriv R.U R z : φ.model.E 0 →ₗ[ℝ] φ.model.E 0),
            ℓ ∘ₗ b = τ → (∀ v, a v ∈ LinearMap.ker ℓ) → ℓ ∘ₗ (b + a) = τ := by
  obtain ⟨φ, hφ, hx, R, hR, z, hz, hsurj⟩ := h
  set ℓ := (scDeriv (F := ScBanach.const ℝ) R.U ((t ∘ φ.symm) ∘ R) z :
      φ.model.E 0 →ₗ[ℝ] ℝ) ∘ₗ
    (LinearMap.range (scDeriv R.U R z : φ.model.E 0 →ₗ[ℝ] φ.model.E 0)).subtype with hℓdef
  have hℓ : ℓ ≠ 0 := by
    intro h0
    obtain ⟨v, hv⟩ := hsurj 1
    have h1 : ℓ ⟨scDeriv R.U R z v, v, rfl⟩ = 1 := hv
    rw [h0] at h1
    exact zero_ne_one h1
  obtain ⟨e, -, he0, he⟩ := exists_isCompl_ker_of_ne_zero hℓ (D := univ) Submodule.span_univ
  have hne : e ≠ 0 := fun h0 => he0 (by rw [h0, map_zero])
  exact ⟨φ, hφ, hx, R, hR, z, hz, ℓ, rfl, hℓ, ℝ ∙ e, finrank_span_singleton hne, he,
    fun S _ _ τ => lemma_5_3_16_preprint hℓ he τ⟩

end Lemma5316

section EmptyRestriction

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

/-- Every map is sc-smooth on the empty retract (as `isScSmoothRetractMap_empty` of
`Chapter8/SigmaPolyfold.lean`, reproved to keep Chapter 5's imports). -/
theorem isScSmoothRetractMap_of_domain_empty {E : ScBanach} {C : Set (E 0)} {E' : ScBanach}
    {C' O' : Set (E' 0)} (f : E 0 → E' 0) : IsScSmoothRetractMap E C ∅ E' C' O' f :=
  IsScSmoothRetractMap.of_locally (mapsTo_empty _ _) fun x hx => absurd hx (notMem_empty x)

/-- Over the empty set the end conditions of Definition 5.3.13 hold: `∅` is a tame
sub-M-polyfold (its atlas has no charts) and every section over it is tame sc-Fredholm. -/
theorem StrongBundle.isCompactFredholmRestriction_of_eq_empty {f : X → Y} (hf : IsSection P f)
    {A : Set X} (hA : A = ∅) : B.IsCompactFredholmRestriction f hf A := by
  subst hA
  refine ⟨fun a ha => absurd ha (notMem_empty a), ?_, ?_⟩
  · refine ⟨_, MAtlas.Equiv.refl _, fun φ hφ => ?_⟩
    obtain ⟨_, _, _, a₀, _⟩ := hφ
    exact absurd a₀.2 (notMem_empty _)
  · exact
      { isScSmooth := ⟨fun x => isEmptyElim x, isOpen_univ, fun x _ => isEmptyElim x,
          fun φ ψ _ _ V _ _ _ => by
            rw [Set.eq_empty_of_isEmpty V, image_empty]
            exact isScSmoothRetractMap_of_domain_empty _⟩
        regularizing := fun _ x _ _ => isEmptyElim x
        germ := fun x _ => isEmptyElim x
        germTame := fun x _ => isEmptyElim x }

end EmptyRestriction

namespace GenCompactHomotopyWitness

section Witness

open TrivialBundle

/-- The witness time function `t(x) = 1/2 + arctan(x)/π` on `ℝ`, with values in `(0, 1)`. -/
def arctanTime (x : Fin 1 → ℝ) : ℝ := 1 / 2 + Real.arctan (x 0) / Real.pi

/-- `t` is `C^∞`. -/
lemma contDiff_arctanTime : ContDiff ℝ ∞ arctanTime :=
  contDiff_const.add ((Real.contDiff_arctan.comp (contDiff_apply ℝ ℝ 0)).div_const _)

/-- `0 < t(x) < 1`. -/
lemma arctanTime_mem_Ioo (x : Fin 1 → ℝ) : arctanTime x ∈ Ioo (0 : ℝ) 1 := by
  have h1 := Real.neg_pi_div_two_lt_arctan (x 0)
  have h2 := Real.arctan_lt_pi_div_two (x 0)
  have hπ := Real.pi_pos
  constructor
  · unfold arctanTime
    have : -(1 / 2 : ℝ) < Real.arctan (x 0) / Real.pi := by
      rw [lt_div_iff₀ hπ]; linarith
    linarith
  · unfold arctanTime
    have : Real.arctan (x 0) / Real.pi < 1 / 2 := by
      rw [div_lt_iff₀ hπ]; linarith
    linarith

/-- `t'(z) = (1/π) · 1/(1 + z²)`. -/
lemma hasFDerivAt_arctanTime (z : Fin 1 → ℝ) :
    HasFDerivAt arctanTime ((1 / Real.pi * (1 / (1 + z 0 ^ 2))) •
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) z := by
  have h1 : HasFDerivAt (fun x : Fin 1 → ℝ => x 0)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) z :=
    hasFDerivAt_apply 0 z
  have h2 := (Real.hasDerivAt_arctan (z 0)).comp_hasFDerivAt z h1
  have h3 := (h2.const_mul (1 / Real.pi)).const_add (1 / 2)
  rw [smul_smul] at h3
  have he : arctanTime =
      fun x => 1 / 2 + 1 / Real.pi * (Real.arctan ∘ fun x : Fin 1 → ℝ => x 0) x := by
    funext x
    simp only [arctanTime, Function.comp]
    ring
  rw [he]
  exact h3

end Witness

section WitnessHomotopy

open TrivialBundle

/-- `dt(x)` is onto at every point, in the chart `rnChart 1 0` with the identity retraction. -/
theorem hasSurjDerivAt_arctanTime (x : Fin 1 → ℝ) : (rnPolyfold 1).HasSurjDerivAt arctanTime x := by
  refine ⟨rnChart 1 0, isChart_rnChart 0, mem_univ x, ScRetraction.id (rn_relOpen_univ 1),
    image_id _, x, ?_, fun a => ?_⟩
  · change (ScBanach.const (Fin 1 → ℝ)).toBase 1 x = x - 0
    rw [ScBanach.const_toBase, sub_zero]
  set c : ℝ := 1 / Real.pi * (1 / (1 + x 0 ^ 2)) with hc
  have hc0 : c ≠ 0 := by
    have : 0 < 1 + x 0 ^ 2 := by positivity
    have := Real.pi_pos
    positivity
  refine ⟨fun _ => a / c, ?_⟩
  have hid := scDeriv_univ_const (V := Fin 1 → ℝ) (V' := Fin 1 → ℝ) contDiff_id x
  rw [fderiv_id] at hid
  have hg : (fun r : Fin 1 → ℝ => arctanTime (r + 0)) = arctanTime := by
    funext r; rw [add_zero]
  have hgd := scDeriv_univ_const (V := Fin 1 → ℝ) (V' := ℝ) contDiff_arctanTime x
  rw [(hasFDerivAt_arctanTime x).fderiv, ← hc] at hgd
  change scDeriv (E := ScBanach.const (Fin 1 → ℝ)) (F := ScBanach.const ℝ) univ
      (fun r : Fin 1 → ℝ => arctanTime (r + 0)) x
      (scDeriv (E := ScBanach.const (Fin 1 → ℝ)) (F := ScBanach.const (Fin 1 → ℝ)) univ
        _root_.id x (fun _ => a / c)) = a
  rw [hg, hid, hgd]
  simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  field_simp

/-- The solution set of the graph section of `id` is `{0}`. -/
theorem solutionSet_graphSection_id :
    solutionSet (proj 1 1) (graphSection (_root_.id : (Fin 1 → ℝ) → (Fin 1 → ℝ))) = {0} := by
  ext x
  simp only [solutionSet, mem_ofPred_eq, isZeroAt_graphSection_iff, id_eq, mem_singleton_iff]

/-- `t⁻¹(0)` and `t⁻¹(1)` are empty. -/
theorem arctanTime_preimage_eq_empty {i : ℝ} (hi : i ∈ ({0, 1} : Set ℝ)) :
    arctanTime ⁻¹' {i} = ∅ := by
  refine eq_empty_of_forall_notMem fun x hx => ?_
  have h := arctanTime_mem_Ioo x
  rw [mem_preimage, mem_singleton_iff.1 hx] at *
  rcases hi with rfl | rfl
  · exact lt_irrefl _ h.1
  · exact lt_irrefl _ h.2

/-- **Satisfiability of 2021 Definition 5.3.13**: the trivial bundle `ℝ × ℝ → ℝ`, the graph
section of `id` (zero set `{0}`) and `t(x) = 1/2 + arctan(x)/π` form a generalized compact
homotopy (between empty problems). -/
theorem isSubmersiveGenCompactHomotopy_witness :
    (bundle 1 1).IsSubmersiveGenCompactHomotopy
      (graphSection (_root_.id : (Fin 1 → ℝ) → (Fin 1 → ℝ))) arctanTime where
  isTame := rnPolyfold_isTame
  isScFredholm := isScFredholmSectionTame_graphSection contDiff_id
  isCompact := solutionSet_graphSection_id ▸ isCompact_singleton
  isScSmooth_t := isScSmoothMap_rn_real_of_contDiff contDiff_arctanTime
  mem_Icc x := Ioo_subset_Icc_self (arctanTime_mem_Ioo x)
  ends _ hi := StrongBundle.isCompactFredholmRestriction_of_eq_empty _
    (arctanTime_preimage_eq_empty hi)
  surjDeriv x _ := hasSurjDerivAt_arctanTime x

/-- The witness is not a generalized compact homotopy in the 2014/2017 reading (`t` is not onto
`[0, 1]`): the 2021 data do not imply the old ones. -/
theorem not_isGenCompactHomotopy_witness :
    ¬ (bundle 1 1).IsGenCompactHomotopy
      (graphSection (_root_.id : (Fin 1 → ℝ) → (Fin 1 → ℝ))) arctanTime := by
  intro h
  have h0 : (0 : ℝ) ∈ range arctanTime := h.range_t ▸ left_mem_Icc.2 zero_le_one
  obtain ⟨x, hx⟩ := h0
  exact lt_irrefl _ (hx ▸ (arctanTime_mem_Ioo x).1)

end WitnessHomotopy

end GenCompactHomotopyWitness

end Polyfold
