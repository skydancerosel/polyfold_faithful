import Polyfold.Chapter15.P3W6R6_RelativeParametric
import Polyfold.Chapter14.P3W6A6_Theorem1419

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, **Theorem 15.3.9
(Transversal Extension Theorem)**, p. 694 (2017: Theorem 15.5), built on A6's form of Theorem
14.1.9 (`theorem_14_1_9_charged_a6`, with tame strong bundle charts and `ChargesBoundary Λ`).

# Theorem 15.3.9 for boundary data that charge every fibre

## Why the charged form

A6 (`not_theorem_14_1_9_statement_a6`) shows that B1's `theorem_14_1_9_statement` does not hold
as we read it whenever `∂X ≠ ∅`: B1's boundary structures allow empty index sets, so `Λ = 0` over
`∂X` is boundary-structurable, while a structurable `Λ'` has total weight `1` on every fibre.
The same applies to the conclusion of Theorem 15.3.9: a structurable `Λ'` with `Λ' = Λ` over
`∂X` forces `Λ` to charge every fibre over `∂X` (`chargesBoundary_of_theorem_15_3_9_r6`).  The
text's "sc⁺-multisection over `∂X`" presumably has non-empty index sets; A6's
`ChargesBoundary Λ` names exactly that.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `theorem_15_3_9_charged_statement A`: TX's `theorem_15_3_9_statement` with tame strong bundle
  charts and `ChargesBoundary Λ` added (`_hyp`-style hypotheses of A6's Theorem 14.1.9).
* `chargesBoundary_of_theorem_15_3_9_r6`: the conclusion forces `ChargesBoundary Λ`.
* `theorem_15_3_9_charged_hyp`: steps (a)–(e) of the proof from TX's relative statement, with
  step (b) A6's unconditional `theorem_14_1_9_charged_a6` and step (a) TY's
  `lemma_15_3_9_cutoff_hyp`.
* `relative_local_families_statement A`: R6's one remaining step, the relative local families
  (`HasLocalGPFamiliesRel` with domain support in `U ∖ ∂X`) under the hypotheses of TX's relative
  statement.
* **`theorem_15_3_9_charged_of_local_rel`**: Theorem 15.3.9 (charged form) from
  `relative_local_families_statement A` alone; the relative parametric step is R6's
  `hasParametricGeneralPositionRel`.
* Witnesses on `ℝⁿ × ℝ⁰ → ℝⁿ` (no boundary).
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

variable (A) in
/-- **Theorem 15.3.9, charged form**: TX's `theorem_15_3_9_statement` with tame strong bundle
charts at every object and `ChargesBoundary Λ` (non-empty index sets over `∂X`) added, the
hypotheses of A6's `theorem_14_1_9_charged_statement`. -/
def theorem_15_3_9_charged_statement : Prop :=
  A.X.IsTame → A.X.HasParacompactOrbitSpace → A.X.PObj.AdmitsScPartitionsOfUnity →
  (∀ x : A.Obj, ∃ c : StrongBundleChart A.X.PObj A.P, A.B.IsTameChart c ∧ x ∈ c.φ.source) →
  ∀ f : A.Obj → A.W, A.E.IsScFredholmSectionFunctor f → A.B.IsScFredholmSectionTame f →
    A.E.HasCompactSolutionSetEp f →
  ∀ (N : A.B.One → ℝ) (U : Set A.Obj), ControlsCompactness A f N U →
  ∀ Λ : A.W → ℚ≥0, IsBoundaryStructurable A Λ → ChargesBoundary Λ → boundaryDomSupp Λ ⊆ U →
    (∀ x ∈ A.X.PObj.boundary, pointwiseNorm N Λ x ≤ 1) →
  ∀ h : A.Obj → ℝ, Continuous h → (∀ φ, h (A.X.src φ) = h (A.X.tgt φ)) →
    (∀ x, 0 < h x ∧ h x ≤ 1) → (∀ x ∈ A.X.PObj.boundary, pointwiseNorm N Λ x < h x) →
    IsBoundaryFaceOnto f Λ →
  ∃ Λ' : A.W → ℚ≥0, IsStructurable A Λ' ∧ (∀ w, A.P w ∈ A.X.PObj.boundary → Λ' w = Λ w) ∧
    domSupp Λ' ⊆ U ∧ (∀ x, pointwiseNorm N Λ' x < h x) ∧ IsAdmissible A f N U Λ' ∧
    IsTransversal f Λ' ∧ A.X.IsBranchedEpSubgroupoid (fun z => (Λ' (f z) : ℚ)) ∧
    A.X.IsCompactBranched (fun z => (Λ' (f z) : ℚ))

/-- **The added hypothesis is necessary**: the conclusion of Theorem 15.3.9 (a structurable `Λ'`
with `Λ' = Λ` over `∂X`) forces `ChargesBoundary Λ` (A6's `chargesBoundary_of_structurable_eq_a6`).
So TX's `theorem_15_3_9_statement` asserts `ChargesBoundary Λ` for every boundary-structurable
`Λ` meeting its other hypotheses. -/
theorem chargesBoundary_of_theorem_15_3_9_r6 {Λ Λ' : A.W → ℚ≥0} (hΛ' : IsStructurable A Λ')
    (h : ∀ w, A.P w ∈ A.X.PObj.boundary → Λ' w = Λ w) : ChargesBoundary Λ :=
  chargesBoundary_of_structurable_eq_a6 hΛ' h

/-- TX's statement gives the charged form (the charged form has more hypotheses). -/
theorem theorem_15_3_9_charged_of_statement (H : theorem_15_3_9_statement A) :
    theorem_15_3_9_charged_statement A :=
  fun hX hpara hPU _ f hf hft hS N U hcc Λ hΛ _ hdomU hN1 h hc hfun hh hNh honto =>
    H hX hpara hPU f hf hft hS N U hcc Λ hΛ hdomU hN1 h hc hfun hh hNh honto

/-- **Proof of Theorem 15.3.9, steps (a)–(e), on A6's Theorem 14.1.9** (TX's `theorem_15_3_9_hyp`
with step (b) A6's unconditional `theorem_14_1_9_charged_a6` and step (a) TY's
`lemma_15_3_9_cutoff_hyp`): only TX's relative statement (steps (c)–(d)) is assumed. -/
theorem theorem_15_3_9_charged_hyp (hrel : theorem_15_3_7_relative_statement A) :
    theorem_15_3_9_charged_statement A := by
  intro hX hpara hPU hB f hf hft hS N U hcc Λ hΛ hch hdomU _ h hc hfun hh hNh honto
  obtain ⟨h₀, h0c, h0nn, h0fun, h0supp, h0lt, h0gt⟩ :=
    lemma_15_3_9_cutoff_hyp hB hX hpara hPU Λ hΛ.1 N hcc.1 U hcc.2.1 hcc.2.2.1 hdomU h hc hfun
      (fun x => (hh x).1) hNh
  obtain ⟨Λ₀, hΛ₀, hΛ₀N, hΛ₀dom, hΛ₀bd⟩ :=
    theorem_14_1_9_charged_a6 hX hpara hPU hB Λ hΛ hch N hcc.1 U hcc.2.1 hcc.2.2.1 hdomU h₀ h0c
      h0nn h0fun h0supp h0gt
  have hsec : IsSection A.P f := hf.1.1.1
  have hgp0 : ∀ x : A.X.PObj.Level 1, A.X.PObj.levelVal 1 x ∈ A.X.PObj.boundary →
      0 < Λ₀ (f (A.X.PObj.levelVal 1 x)) → IsReducedOntoAtPt f Λ₀ x := by
    intro x hx hpos
    have hbd : A.P (f (A.X.PObj.levelVal 1 x)) ∈ A.X.PObj.boundary := by rw [hsec]; exact hx
    have hpos' : 0 < Λ (f (A.X.PObj.levelVal 1 x)) := by rwa [← hΛ₀bd _ hbd]
    exact honto Λ₀ hΛ₀.1 hΛ₀bd x hx (mem_smoothSet_of_pos hft hΛ₀.1 hpos) hpos'
  obtain ⟨Λ', hΛ', hbd', hdom', hN', htr', hgp'⟩ :=
    hrel hX hpara hPU f hf hft hS N U hcc h hc hfun hh Λ₀ hΛ₀ hΛ₀dom
      (fun x => (hΛ₀N x).trans_lt (h0lt x)) hgp0
  have hN1 : ∀ x, pointwiseNorm N Λ' x ≤ 1 := fun x => (hN' x).le.trans (hh x).2
  obtain ⟨hbr, hcpt⟩ := theorem_15_3_7_in_particular_hyp hf hft hcc hΛ'.1 hN1 hdom' hgp'
  exact ⟨Λ', hΛ', fun w hw => (hbd' w hw).trans (hΛ₀bd w hw), hdom', hN',
    isAdmissible_of_domSupp_subset hsec hcc.2.2.2.1 hΛ'.1 hN1 hdom', htr', hbr, hcpt⟩

variable (A) in
/-- **R6's remaining step**: the relative local families of the proof of Theorem 15.3.9 (steps
(c)–(d), "argue as in Theorem 15.3.7"; R6's `HasLocalGPFamiliesRel` with domain support in
`U ∖ ∂X` and size `h − N(Λ₀)`), under the hypotheses of TX's relative statement. -/
def relative_local_families_statement : Prop :=
  A.X.IsTame → A.X.HasParacompactOrbitSpace → A.X.PObj.AdmitsScPartitionsOfUnity →
  ∀ f : A.Obj → A.W, A.E.IsScFredholmSectionFunctor f → A.B.IsScFredholmSectionTame f →
    A.E.HasCompactSolutionSetEp f →
  ∀ (N : A.B.One → ℝ) (U : Set A.Obj), ControlsCompactness A f N U →
  ∀ h : A.Obj → ℝ, Continuous h → (∀ φ, h (A.X.src φ) = h (A.X.tgt φ)) →
    (∀ x, 0 < h x ∧ h x ≤ 1) →
  ∀ Λ₀ : A.W → ℚ≥0, IsStructurable A Λ₀ → domSupp Λ₀ ⊆ U →
    (∀ x, pointwiseNorm N Λ₀ x < h x) →
    (∀ x : A.X.PObj.Level 1, A.X.PObj.levelVal 1 x ∈ A.X.PObj.boundary →
      0 < Λ₀ (f (A.X.PObj.levelVal 1 x)) → IsReducedOntoAtPt f Λ₀ x) →
    HasLocalGPFamiliesRel A f Λ₀ N (U ∩ A.X.PObj.boundaryᶜ)
      (fun x => h x - pointwiseNorm N Λ₀ x)

/-- **Theorem 15.3.9 (Transversal Extension Theorem), p. 694, charged form**, from R6's one
remaining step (`relative_local_families_statement`): Theorem 14.1.9 is A6's unconditional
`theorem_14_1_9_charged_a6`, the cutoff is TY's, the relative parametric step is R6's
`hasParametricGeneralPositionRel`. -/
theorem theorem_15_3_9_charged_of_local_rel (H : relative_local_families_statement A) :
    theorem_15_3_9_charged_statement A :=
  theorem_15_3_9_charged_hyp (theorem_15_3_7_relative_of_local H)

/-- **The charged form holds on `ℝⁿ × ℝ⁰ → ℝⁿ`** (no boundary; TX's witness). -/
theorem theorem_15_3_9_charged_statement_epSEP_zero (n : ℕ) :
    theorem_15_3_9_charged_statement (StrongBundleEquivalenceExamples.epSEP n 0) :=
  theorem_15_3_9_charged_of_statement (theorem_15_3_9_statement_epSEP_zero n)

/-- **R6's remaining step holds on `ℝⁿ × ℝ⁰ → ℝⁿ`** (fibres `0`; a weak witness, no boundary). -/
theorem relative_local_families_statement_epSEP_zero (n : ℕ) :
    relative_local_families_statement (StrongBundleEquivalenceExamples.epSEP n 0) :=
  fun _ _ _ f _ _ _ _ _ hcc _ _ _ _ Λ₀ _ _ _ _ =>
    hasLocalGPFamiliesRel_epSEP_zero n f Λ₀ hcc.1.isAuxNorm _ _

end SBLocalization

end Polyfold
