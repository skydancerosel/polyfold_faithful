import Polyfold.Chapter16.IndexZeroNoBumpsRestr
import Polyfold.Chapter16.InvariantNoBumpsUnconditional

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §16.6, p. 739:
**Theorem 16.6.6** (2017: Theorem 16.8) **for Fredholm index `0`**, with Corollary 15.4.4
(p. 703) and Theorem 15.4.3 (p. 702).

# Theorem 16.6.6 for index `0` over all admissible perturbations, without bump functions

## The text, paraphrased

For Fredholm index `0` the perturbed solution set `θ̂ = λ ∘ f` is a finite set of weighted signed
points, and the invariant is the weighted signed count of a closed `0`-form; it does not depend
on the admissible `λ` (controlled by `(n, U)`, `(f, λ)` in general position).

## What is formalized (namespace `Polyfold.StrongPolyfoldBundle`)

The statements of `Polyfold/Chapter16/IndexZeroAllAdmissible.lean` with the standing hypotheses
`CanonicalGermInput o 0` (tame germ data and index `0` in the model of `o`; no bump functions):

* `theorem_16_6_6_index_zero_solutionSet_noBumps`: every admissible `λ` has a perturbed solution
  set of dimension `0` with the canonical orientation of `(f, o)`.
* **`theorem_16_6_6_index_zero_count_eq_unconditional`**,
  **`theorem_16_6_6_index_zero_all_admissible_unconditional`**,
  `theorem_16_6_6_index_zero_wellDefined_unconditional`: the counts `∫_θ̂ τ`, `∮_θ̂ τ` of a closed
  `0`-form agree over any two of them.

## Reading

As in `theorem_16_6_6_all_admissible_unconditional`: the orientation is the canonical one in the
model of `o`; the ep-groupoid statement is `pointCount_eq_of_isTransversalPerturbation_restr`,
and the local families on the cylinder of a restriction of the model are
`hasRestrictedFamilies_of_germInput`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

namespace StrongPolyfoldBundle

open StrongPolyfoldBundleStructure PolyfoldClass SBLocalization SEP EpGroupoid

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {c : StrongPolyfoldBundle p}

/-- **2021 Theorem 16.6.6, p. 739, index `0`: every admissible `λ` gives a canonically oriented
`θ̂`** of dimension `0`, with no bump functions and no partitions of unity. -/
theorem theorem_16_6_6_index_zero_solutionSet_noBumps (hbd : c.polyfold.boundary = ∅)
    {s : FredholmSection c} {n : Y → ℝ} (hn : c.IsAuxNorm n) {U : Set Z} (hU : IsOpen U)
    (hcc : s.1.ControlsCompactness n U) {o : OrientationRep s}
    (H : CanonicalGermInput o 0) (t : ScPlusMultisection c)
    (ht : t.IsControlledBy n U) (hgp : s.1.IsInGeneralPositionWith t) :
    ∃ Q : PointOrientedPerturbation s.1, Q.t = t ∧ Q.IsAdmissible n U ∧
      IsCanonicalPointSolutionSet o Q := by
  obtain ⟨Λ, hΛ, hl⟩ := exists_functor_rep t o.a.hS
  have ht' : (⟦ofFunctor o.a.S o.a.hS Λ hΛ⟧ : ScPlusMultisection c) = t :=
    mk_ofFunctor_eq t o.a.hS hΛ hl
  have hgpΛ := (ScSection.isInGeneralPositionWith_iff_of_rep s.1 s.2 t o.a o.ha hΛ hl).1 hgp
  rw [← ht'] at ht
  have hd : ∀ x, o.a.S.A.X.PObj.degIndex x = 0 :=
    degIndex_eq_zero_of_boundary_eq_empty hbd o.a.hS
  have hX : o.a.S.A.X.IsTame := o.a.S.A.X.isTame_of_degIndex_eq_zero hd
  have hoL := o.isSectionOrientationLoc hX H.tame
  have hcca := (o.a.controlsCompactness_iff hn hU).1 (by rw [o.ha]; exact hcc)
  set b := ofFunctor o.a.S o.a.hS Λ hΛ
  have hN1 : ∀ x, pointwiseNorm (o.a.S.normOf n) Λ x ≤ 1 := by
    intro x
    rw [← normLam_eq o.a.hS n Λ b.lam x fun w _ => b.comm w]
    exact ht.1 _
  have hdom : domSupp Λ ⊆ o.a.g ⁻¹' U := by
    intro x hx
    apply ht.2
    rw [← remark_16_5_3 b]
    exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  have htr := IsInGeneralPosition.isTransversal o.hF hΛ hgpΛ
  have hgood : ∀ x, 0 < Λ (o.a.F x) → SBLocalization.IsGoodPositionAt o.a.F Λ x :=
    fun x hpos => isGoodPositionAt_of_isInGeneralPosition o.hF H.tame hΛ hgpΛ hpos
  obtain ⟨hbr, hcpt⟩ := theorem_15_4_3_isBranched_hyp o.hF H.tame hcca hΛ hdom hN1 htr
    fun x _ => hgood x
  have hidx : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (o.a.F z) : ℚ)),
      o.a.S.A.B.IsIndexAt o.a.F x (0 : ℕ) := fun x hx =>
    H.index x (mem_smoothSet_of_pos H.tame hΛ (by exact_mod_cast hx))
  have hcan := theorem_15_4_1_of_isSectionOrientationLoc hX o.hF H.tame hΛ o.hsec o.o
    o.isOrientation.2 hoL (fun x hx => hgood x (by exact_mod_cast hx)) hidx
    (o.a.S.A.X.hasIndependentTangentSums _)
  let P : PointSolution o.a.S.A o.a.F :=
    ⟨Λ, hΛ, canonicalOrientation Λ o.hF.2 o.hsec o.o, hbr, hcpt, hcan.1,
      EpGroupoid.isPointTame_iff.2 hcan.loc⟩
  exact ⟨solutionPointPerturbation o.a P o.ha, ht', ⟨ht, o.a, Λ, hΛ, o.ha, rfl, hgpΛ⟩, P, hcan,
    rfl⟩

/-! ### Independence of the perturbation -/

/-- **2021 Theorem 16.6.6, p. 739 (2017: Theorem 16.8), for Fredholm index `0`: the counts do not
depend on the admissible perturbation.**  Let `∂Z = ∅`, `(n, U)` control the compactness of `f`,
and `o` be an orientation of `f` whose model has tame germ data and Fredholm index `0`.  For
perturbed solution sets `θ̂₀`, `θ̂₁` of dimension `0` of admissible
`λ₀`, `λ₁` (controlled by `(n, U)`, in general position; neither structurability nor `n(λ) < 1`
is asked) with the canonical orientation of `(f, o)`, a closed `0`-form `τ` has the same weighted
signed count and the same effective count.  Neither bump functions nor partitions of unity are
assumed. -/
theorem theorem_16_6_6_index_zero_count_eq_unconditional (hbd : c.polyfold.boundary = ∅)
    {s : FredholmSection c} {n : Y → ℝ} (hn : c.IsAuxNorm n) {U : Set Z} (hU : IsOpen U)
    (hcc : s.1.ControlsCompactness n U) {o : OrientationRep s} (H : CanonicalGermInput o 0)
    {Q₀ Q₁ : PointOrientedPerturbation s.1}
    (a₀ : Q₀.IsAdmissible n U) (c₀ : IsCanonicalPointSolutionSet o Q₀)
    (a₁ : Q₁.IsAdmissible n U) (c₁ : IsCanonicalPointSolutionSet o Q₁)
    (τ : ScForm c.polyfold 0) (hτ : ScForm.d τ = 0) :
    Q₀.count τ = Q₁.count τ ∧ Q₀.countEff τ = Q₁.countEff τ := by
  obtain ⟨P₀, hT₀, rfl⟩ := c₀
  obtain ⟨P₁, hT₁, rfl⟩ := c₁
  have hd : ∀ x, o.a.S.A.X.PObj.degIndex x = 0 :=
    degIndex_eq_zero_of_boundary_eq_empty hbd o.a.hS
  have hX : o.a.S.A.X.IsTame := o.a.S.A.X.isTame_of_degIndex_eq_zero hd
  have hoL := o.isSectionOrientationLoc hX H.tame
  have hr₀ := isTransversalPerturbation_of_isAdmissible_point hn hU hcc P₀ a₀
  have hr₁ := isTransversalPerturbation_of_isAdmissible_point hn hU hcc P₁ a₁
  have hq := toPolyfoldStructure_mem o.a.hS
  have hω : o.a.S.A.baseEP.epFormsInftyD 0
      (ScForm.toStructure o.a.S.toPolyfoldStructure hq τ) = 0 := by
    have h : o.a.S.toPolyfoldStructure.X.epFormsInftyD 0
        (ScForm.toStructure o.a.S.toPolyfoldStructure hq τ) = 0 := by
      rw [← ScForm.toStructure_dFun, ← ScForm.d_apply, hτ, ScForm.toStructure_zero]
    exact h
  have hidx : ∀ x ∈ o.a.S.A.X.PObj.smoothSet, o.a.S.A.B.IsIndexAt o.a.F x 0 :=
    fun x hx => by exact_mod_cast H.index x hx
  obtain ⟨e, eE⟩ := pointCount_eq_of_isTransversalPerturbation_restr hd o.hF H.tame o.hsec o.o
    o.isOrientation.2 hoL hidx o.a.S.paracompact hr₀ hr₁ hT₀ hT₁
    (hasRestrictedFamilies_of_germInput hbd H n U hr₀ hr₁) _ hω
  refine ⟨?_, ?_⟩
  · change (solutionPointSuborbifold o.a P₀).count τ = (solutionPointSuborbifold o.a P₁).count τ
    rw [count_solutionPointSuborbifold, count_solutionPointSuborbifold]
    exact e
  · change (solutionPointSuborbifold o.a P₀).countEff τ =
      (solutionPointSuborbifold o.a P₁).countEff τ
    rw [countEff_solutionPointSuborbifold, countEff_solutionPointSuborbifold]
    exact eE _

/-- **2021 Theorem 16.6.6, p. 739, for Fredholm index `0`, over all admissible perturbations**:
`theorem_16_6_6_index_zero_polyfold_statement` for the predicate "`θ̂` carries the canonical
orientation of `(f, o)`", with the standing hypotheses `CanonicalGermInput o 0` (tame germ data,
index `0`).  Neither bump functions nor partitions of unity are assumed, and the compactness of the
solution set of `f` is used only through `(n, U)`
controlling compactness. -/
theorem theorem_16_6_6_index_zero_all_admissible_unconditional (s : FredholmSection c) (n : Y → ℝ)
    (U : Set Z) :
    theorem_16_6_6_index_zero_polyfold_statement s n U
      (fun o Q => CanonicalGermInput o 0 ∧ IsCanonicalPointSolutionSet o Q) := by
  rintro hbd - hn hU hcc o Q₀ Q₁ a₀ ⟨H, c₀⟩ a₁ ⟨-, c₁⟩ τ hτ
  exact theorem_16_6_6_index_zero_count_eq_unconditional hbd hn hU hcc H a₀ c₀ a₁ c₁ τ hτ

/-- **2021 Theorem 16.6.6, p. 739, index `0`, existence and independence over all admissible
`λ`**: every sc⁺-multisection `λ` controlled by `(n, U)` with `(f, λ)` in general position has a
perturbed solution set of dimension `0` with the canonical orientation of `(f, o)`, and the
counts `∫_θ̂ τ`, `∮_θ̂ τ` of a closed `0`-form agree over any two of them.  Neither bump functions
nor partitions of unity are assumed. -/
theorem theorem_16_6_6_index_zero_wellDefined_unconditional (hbd : c.polyfold.boundary = ∅)
    {s : FredholmSection c} {n : Y → ℝ} (hn : c.IsAuxNorm n) {U : Set Z} (hU : IsOpen U)
    (hcc : s.1.ControlsCompactness n U) {o : OrientationRep s} (H : CanonicalGermInput o 0) :
    (∀ t : ScPlusMultisection c, t.IsControlledBy n U → s.1.IsInGeneralPositionWith t →
      ∃ Q : PointOrientedPerturbation s.1, Q.t = t ∧ Q.IsAdmissible n U ∧
        IsCanonicalPointSolutionSet o Q) ∧
    ∀ Q₀ Q₁ : PointOrientedPerturbation s.1, Q₀.IsAdmissible n U →
      IsCanonicalPointSolutionSet o Q₀ → Q₁.IsAdmissible n U →
      IsCanonicalPointSolutionSet o Q₁ →
      ∀ τ : ScForm c.polyfold 0, ScForm.d τ = 0 →
        Q₀.count τ = Q₁.count τ ∧ Q₀.countEff τ = Q₁.countEff τ :=
  ⟨fun t ht hgp => theorem_16_6_6_index_zero_solutionSet_noBumps hbd hn hU hcc H t ht hgp,
    fun _ _ a₀ c₀ a₁ c₁ τ hτ =>
      theorem_16_6_6_index_zero_count_eq_unconditional hbd hn hU hcc H a₀ c₀ a₁ c₁ τ hτ⟩

end StrongPolyfoldBundle

end Polyfold
