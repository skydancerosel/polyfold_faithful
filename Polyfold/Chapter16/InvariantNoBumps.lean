import Polyfold.Chapter16.InvariantAllAdmissible
import Polyfold.Chapter16.OrientationRepLocalNoBumps
import Polyfold.Chapter15.RestrictedCobordism
import Polyfold.Chapter15.CanonicalLiftContinuityLocal

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §16.6, p. 739:
**Theorem 16.6.6** (2017: Theorem 16.8), with Definition 16.6.5 (p. 739), Theorem 15.4.3 and
Corollary 15.4.4 (pp. 702–703).

# Theorem 16.6.6 over all admissible perturbations, without bump functions in the model

## The text, paraphrased

(Theorem 16.6.6) Let `∂Z = ∅`, `f` be an oriented sc-Fredholm section with compact solution set
and `(n, U)` control compactness.  For an sc⁺-multisection `λ` controlled by `(n, U)` with
`(f, λ)` in general position, the branched integrals of a closed form over `λ ∘ f` do not depend
on `λ`.

## What is formalized (namespace `Polyfold.StrongPolyfoldBundle`)

* `CanonicalGermInput o k`: tame germ data of the representative `F` and index `k` at the smooth
  points (the fields of `CanonicalBumpInput` other than the bump functions).
* `HasRestrictedFamilies o n U`: any two transversal perturbations of the model controlled by
  `(n, U)` have the local families on the cylinder of a restriction of the model to a saturated
  open neighbourhood of the compact set (`SBLocalization.HasRestrictedCylinderFamilies`).
* **`theorem_16_6_6_solutionSet_noBumps`**: every admissible `λ` has a compact tame `θ̂ = λ ∘ f`
  with the canonical orientation of `(f, o)`; no bump functions.
* **`theorem_16_6_6_integral_eq_of_restrictedFamilies`**,
  `theorem_16_6_6_all_admissible_of_restrictedFamilies`,
  `theorem_16_6_6_wellDefined_of_restrictedFamilies`: the independence of the admissible
  perturbation, with `HasRestrictedFamilies` in place of the bump functions.

## Reading

The orientation `o` of Definition 16.6.5 is continuous in the local orientation sets
(`OrientationRep.isSectionOrientationLoc`), Theorem 15.4.1 is
`theorem_15_4_1_of_isSectionOrientationLoc`, and the cobordism argument runs on the restriction of
the model to a neighbourhood of the compact set
(`SBLocalization.integral_eq_of_isTransversalPerturbation_restr`).
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

/-! ### The standing hypotheses -/

/-- **The standing hypotheses of Theorem 16.6.6 in the model of an orientation `o`**, Fredholm
index `k`, without bump functions: tame germ data of the representative `F`, and index `k` at
every smooth point. -/
structure CanonicalGermInput {s : FredholmSection c} (o : OrientationRep s) (k : ℕ) : Prop where
  tame : o.a.S.A.B.IsScFredholmSectionTame o.a.F
  index : ∀ x ∈ o.a.S.A.X.PObj.smoothSet, o.a.S.A.B.IsIndexAt o.a.F x (k : ℤ)

theorem CanonicalBumpInput.canonicalGermInput {s : FredholmSection c} {o : OrientationRep s}
    {k : ℕ} (H : CanonicalBumpInput o k) : CanonicalGermInput o k :=
  ⟨H.tame, H.index⟩

/-- **Local families near the compact set, in the model of `o`**: any two transversal
perturbations of the model controlled by `(n, U)` have the local families of the relative step on
the cylinder of a restriction of the model to a saturated open neighbourhood of the compact
set. -/
def HasRestrictedFamilies {s : FredholmSection c} (o : OrientationRep s) (n : Y → ℝ)
    (U : Set Z) : Prop :=
  ∀ ⦃Λ₀ Λ₁ : o.a.S.A.W → ℚ≥0⦄,
    IsTransversalPerturbation o.a.S.A o.a.F (o.a.S.normOf n) (o.a.g ⁻¹' U) Λ₀ →
    IsTransversalPerturbation o.a.S.A o.a.F (o.a.S.normOf n) (o.a.g ⁻¹' U) Λ₁ →
    HasRestrictedCylinderFamilies o.a.S.A o.a.F o.hF (o.a.S.normOf n) (o.a.S.normOf n)
      (o.a.g ⁻¹' U) (o.a.g ⁻¹' U) Λ₀ Λ₁

/-! ### Existence -/

/-- **2021 Theorem 16.6.6, p. 739: every admissible `λ` gives a canonically oriented `θ̂`**, with
no bump functions and no partitions of unity: for every sc⁺-multisection
`t` controlled by `(n, U)` with `(f, t)` in general position, `θ̂ = t ∘ f` is a compact tame
oriented branched suborbifold of dimension `m + 1` carrying the canonical orientation of
`(f, o)`. -/
theorem theorem_16_6_6_solutionSet_noBumps (hbd : c.polyfold.boundary = ∅)
    {s : FredholmSection c} {n : Y → ℝ} (hn : c.IsAuxNorm n) {U : Set Z} (hU : IsOpen U)
    (hcc : s.1.ControlsCompactness n U) {m : ℕ} {o : OrientationRep s}
    (H : CanonicalGermInput o (m + 1)) (t : ScPlusMultisection c)
    (ht : t.IsControlledBy n U) (hgp : s.1.IsInGeneralPositionWith t) :
    ∃ Q : OrientedPerturbation s.1 m, Q.t = t ∧ Q.IsAdmissible n U ∧
      IsCanonicalSolutionSet o Q := by
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
      o.a.S.A.B.IsIndexAt o.a.F x (m + 1 : ℕ) := fun x hx =>
    H.index x (mem_smoothSet_of_pos H.tame hΛ (by exact_mod_cast hx))
  have hcan := theorem_15_4_1_of_isSectionOrientationLoc hX o.hF H.tame hΛ o.hsec o.o
    o.isOrientation.2 hoL (fun x hx => hgood x (by exact_mod_cast hx)) hidx
    (o.a.S.A.X.hasIndependentTangentSums _)
  let M : ModelSolutionSet o.a m :=
    ⟨Λ, hΛ, canonicalOrientation Λ o.hF.2 o.hsec o.o, hbr, hcpt, hcan.1, hcan.loc⟩
  exact ⟨M.toOrientedPerturbation o.ha, ht', ⟨ht, o.a, Λ, hΛ, o.ha, rfl, hgpΛ⟩, M, hcan, rfl⟩

/-! ### Independence of the perturbation -/

set_option maxHeartbeats 800000 in
-- the cylinder of the model is unfolded in the hypotheses of the ep-groupoid statement
/-- **2021 Theorem 16.6.6, p. 739 (2017: Theorem 16.8): the integrals do not depend on the
admissible perturbation.**  Let `∂Z = ∅`, `(n, U)` control the compactness of `f`, and `o` be an
orientation of `f` (Definition 16.6.5) whose model has tame germ data, the local families `hR`
and Fredholm index `m + 1`.  Let `θ̂₀ = λ₀ ∘ f` and `θ̂₁ = λ₁ ∘ f` be perturbed solution sets of
admissible `λ₀`, `λ₁` (controlled by `(n, U)`, in general position; neither structurability nor
`n(λ) < 1` is asked), with the canonical orientation of `(f, o)`.  Then `∫_{θ̂₀} τ = ∫_{θ̂₁} τ`
and `∮_{θ̂₀} τ = ∮_{θ̂₁} τ` for every closed `τ`.  No bump functions and no partitions of unity are
assumed. -/
theorem theorem_16_6_6_integral_eq_of_restrictedFamilies (hbd : c.polyfold.boundary = ∅) {s : FredholmSection c}
    {n : Y → ℝ} (hn : c.IsAuxNorm n) {U : Set Z} (hU : IsOpen U)
    (hcc : s.1.ControlsCompactness n U) {m : ℕ} {o : OrientationRep s}
    (H : CanonicalGermInput o (m + 1)) (hR : HasRestrictedFamilies o n U)
    {Q₀ Q₁ : OrientedPerturbation s.1 m}
    (a₀ : Q₀.IsAdmissible n U) (c₀ : IsCanonicalSolutionSet o Q₀)
    (a₁ : Q₁.IsAdmissible n U) (c₁ : IsCanonicalSolutionSet o Q₁)
    (τ : ScForm c.polyfold (m + 1)) (hτ : ScForm.d τ = 0) :
    Q₀.integral τ = Q₁.integral τ ∧ Q₀.integralEff τ = Q₁.integralEff τ := by
  obtain ⟨M₀, hT₀, rfl⟩ := c₀
  obtain ⟨M₁, hT₁, rfl⟩ := c₁
  have hd : ∀ x, o.a.S.A.X.PObj.degIndex x = 0 :=
    degIndex_eq_zero_of_boundary_eq_empty hbd o.a.hS
  have hpara := o.a.S.paracompact
  have hX : o.a.S.A.X.IsTame := o.a.S.A.X.isTame_of_degIndex_eq_zero hd
  have hoL := o.isSectionOrientationLoc hX H.tame
  have hLUC := o.a.S.A.X.proposition_7_4_10_of_isZhou o.a.S.isZhou
  have hr₀ := M₀.isTransversalPerturbation hn hU hcc a₀
  have hr₁ := M₁.isTransversalPerturbation hn hU hcc a₁
  have hq := toPolyfoldStructure_mem o.a.hS
  have hω : o.a.S.A.baseEP.epFormsInftyD (m + 1)
      (ScForm.toStructure o.a.S.toPolyfoldStructure hq τ) = 0 := by
    have h : o.a.S.toPolyfoldStructure.X.epFormsInftyD (m + 1)
        (ScForm.toStructure o.a.S.toPolyfoldStructure hq τ) = 0 := by
      rw [← ScForm.toStructure_dFun, ← ScForm.d_apply, hτ, ScForm.toStructure_zero]
    exact h
  have e := integral_eq_of_isTransversalPerturbation_restr hd o.hF H.tame o.hsec o.o
    o.isOrientation.2 hoL H.index hpara (S₀ := M₀.toSolution) (S₁ := M₁.toSolution) hr₀ hr₁
    hT₀ hT₁ (hR hr₀ hr₁) _ hω
  have eE := integralEff_eq_of_isTransversalPerturbation_restr hd o.hF H.tame o.hsec o.o
    o.isOrientation.2 hoL H.index hpara hLUC (S₀ := M₀.toSolution) (S₁ := M₁.toSolution)
    hr₀ hr₁ hT₀ hT₁ (hR hr₀ hr₁) _ hω
  have i₀ := M₀.integral_toCompact (ScForm.toStructure o.a.S.toPolyfoldStructure hq τ)
  have i₁ := M₁.integral_toCompact (ScForm.toStructure o.a.S.toPolyfoldStructure hq τ)
  have j₀ := M₀.integralEff_toCompact (ScForm.toStructure o.a.S.toPolyfoldStructure hq τ)
  have j₁ := M₁.integralEff_toCompact (ScForm.toStructure o.a.S.toPolyfoldStructure hq τ)
  rw [ScForm.mk_toStructure] at i₀ i₁ j₀ j₁
  exact ⟨i₀.trans (e.trans i₁.symm), j₀.trans (eE.trans j₁.symm)⟩

/-- **2021 Theorem 16.6.6, p. 739 (2017: Theorem 16.8), over all admissible perturbations.**
For `∂Z = ∅`, `f` with `(n, U)` controlling compactness and every orientation `o` of `f` whose
model has tame germ data, the local families and Fredholm index `m + 1`: over the admissible
perturbed solution sets `θ̂ = λ ∘ f` (`λ` controlled by `(n, U)`, `(f, λ)` in general position)
with the canonical orientation of `(f, o)` (Definition 15.4.2 in the model of `o`), `∫_θ̂ τ` and
`∮_θ̂ τ` depend only on `[τ]`, and a closed `τ` has the same `∫_θ̂ τ` and `∮_θ̂ τ` for any two of
them.  No bump functions and no partitions of unity are assumed. -/
theorem theorem_16_6_6_all_admissible_of_restrictedFamilies (s : FredholmSection c) (n : Y → ℝ) (U : Set Z) (m : ℕ) :
    theorem_16_6_6_statement s n U m
      (fun o Q => CanonicalGermInput o (m + 1) ∧ HasRestrictedFamilies o n U ∧
        IsCanonicalSolutionSet o Q) := by
  intro hbd _ hn hU hcc o
  refine ⟨fun P _ _ τ η =>
    P.toCompactOrientedSuborbifold.integral_add_d_of_boundary_eq_empty hbd τ η, ?_⟩
  rintro P₀ P₁ a₀ ⟨H, hR, c₀⟩ a₁ ⟨-, -, c₁⟩ τ hτ
  exact theorem_16_6_6_integral_eq_of_restrictedFamilies hbd hn hU hcc H hR a₀ c₀ a₁ c₁ τ hτ

/-- **2021 Theorem 16.6.6, p. 739, existence and independence over all admissible `λ`.**  Under
the hypotheses of `theorem_16_6_6_all_admissible_of_restrictedFamilies`: (1) every sc⁺-multisection `λ` controlled by
`(n, U)` with `(f, λ)` in general position has a perturbed solution set `θ̂ = λ ∘ f`, compact,
tame and oriented of dimension `m + 1`, with the canonical orientation of `(f, o)`; (2) for any two
such `θ̂`, of the same or of different `λ`, the integrals `∫_θ̂ τ` and `∮_θ̂ τ` of a closed `τ`
agree; (3) they depend only on `[τ]`. -/
theorem theorem_16_6_6_wellDefined_of_restrictedFamilies (hbd : c.polyfold.boundary = ∅)
    {s : FredholmSection c} {n : Y → ℝ} (hn : c.IsAuxNorm n) {U : Set Z} (hU : IsOpen U)
    (hcc : s.1.ControlsCompactness n U) {m : ℕ} {o : OrientationRep s}
    (H : CanonicalGermInput o (m + 1)) (hR : HasRestrictedFamilies o n U) :
    (∀ t : ScPlusMultisection c, t.IsControlledBy n U → s.1.IsInGeneralPositionWith t →
      ∃ Q : OrientedPerturbation s.1 m, Q.t = t ∧ Q.IsAdmissible n U ∧
        IsCanonicalSolutionSet o Q) ∧
    (∀ Q₀ Q₁ : OrientedPerturbation s.1 m, Q₀.IsAdmissible n U → IsCanonicalSolutionSet o Q₀ →
      Q₁.IsAdmissible n U → IsCanonicalSolutionSet o Q₁ →
      ∀ τ : ScForm c.polyfold (m + 1), ScForm.d τ = 0 →
        Q₀.integral τ = Q₁.integral τ ∧ Q₀.integralEff τ = Q₁.integralEff τ) ∧
    ∀ Q : OrientedPerturbation s.1 m, ∀ (τ : ScForm c.polyfold (m + 1))
      (η : ScForm c.polyfold m),
      Q.integral (τ + ScForm.d η) = Q.integral τ ∧
        Q.integralEff (τ + ScForm.d η) = Q.integralEff τ :=
  ⟨fun t ht hgp => theorem_16_6_6_solutionSet_noBumps hbd hn hU hcc H t ht hgp,
    fun _ _ a₀ c₀ a₁ c₁ τ hτ =>
      theorem_16_6_6_integral_eq_of_restrictedFamilies hbd hn hU hcc H hR a₀ c₀ a₁ c₁ τ hτ,
    fun Q τ η => Q.toCompactOrientedSuborbifold.integral_add_d_of_boundary_eq_empty hbd τ η⟩

end StrongPolyfoldBundle

end Polyfold
