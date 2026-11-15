import Polyfold.Chapter15.RelativeParametric
import Polyfold.Chapter14.BoundaryExtensionTheorem
import Polyfold.Chapter10.TameBundleCharts

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, **Theorem 15.3.9
(Transversal Extension Theorem)**, p. 694 (2017: Theorem 15.5), built on Theorem 14.1.9 in the
form `theorem_14_1_9_charged_a6` (tame strong bundle charts, `ChargesBoundary Λ`).

# Theorem 15.3.9 from Theorem 14.1.9

## The charged form

`theorem_15_3_9_charged_statement` lists tame strong bundle charts and `ChargesBoundary Λ` among
the hypotheses, as the charged Theorem 14.1.9 does.  Both are automatic: a strong bundle over a tame
ep-groupoid has tame strong bundle charts (`SEP.exists_isTameChart`), and the index sets of
Definition 14.1.3 are non-empty, so a structurable `Λ` over `∂X` charges every boundary fibre
(`IsBoundaryStructurable.chargesBoundary`).
It is also forced by the conclusion: a structurable `Λ'` with `Λ' = Λ` over `∂X` charges every
fibre (`chargesBoundary_of_theorem_15_3_9_r6`).

## What is formalized (namespace `Polyfold.SBLocalization`)

* `theorem_15_3_9_charged_statement A`: `theorem_15_3_9_statement` with tame strong bundle
  charts and `ChargesBoundary Λ` added (the hypotheses of the charged Theorem 14.1.9).
* `theorem_15_3_9_statement_of_charged`, `theorem_15_3_9_charged_iff`: the charged form and the
  uncharged statement are equivalent (tame strong bundle charts: `SEP.exists_isTameChart`).
* `lemma_15_3_9_cutoff`: step (a), the cut-off, with no added hypothesis.
* `chargesBoundary_of_theorem_15_3_9_r6`: the conclusion forces `ChargesBoundary Λ`.
* `theorem_15_3_9_charged_hyp`: steps (a)–(e) of the proof from the relative statement, with
  step (b) unconditional `theorem_14_1_9_charged_a6` and step (a)
  `lemma_15_3_9_cutoff_hyp`.
* **`theorem_15_3_9_of_rel`**: `theorem_15_3_9_statement A` from the relative statement
  (steps (c)–(d)) alone; `theorem_15_3_9_hyp` with its hypotheses on Theorem 14.1.9
  (`theorem_14_1_9`) and the cut-off discharged.
* `relative_local_families_statement A`: the one remaining step, the relative local families
  (`HasLocalGPFamiliesRel` with domain support in `U ∖ ∂X`) under the hypotheses of the relative
  statement.
* **`theorem_15_3_9_charged_of_local_rel`**, **`theorem_15_3_9_of_local_families`**: Theorem
  15.3.9 (charged form, and the uncharged statement) from
  `relative_local_families_statement A` alone; the relative parametric step is
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
/-- **Theorem 15.3.9, charged form**: `theorem_15_3_9_statement` with tame strong bundle
charts at every object and `ChargesBoundary Λ` (non-empty index sets over `∂X`) added, the
hypotheses of `theorem_14_1_9_charged_statement`. -/
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
with `Λ' = Λ` over `∂X`) forces `ChargesBoundary Λ` (`chargesBoundary_of_structurable_eq_a6`).
So `theorem_15_3_9_statement` asserts `ChargesBoundary Λ` for every boundary-structurable
`Λ` meeting its other hypotheses. -/
theorem chargesBoundary_of_theorem_15_3_9_r6 {Λ Λ' : A.W → ℚ≥0} (hΛ' : IsStructurable A Λ')
    (h : ∀ w, A.P w ∈ A.X.PObj.boundary → Λ' w = Λ w) : ChargesBoundary Λ :=
  chargesBoundary_of_structurable_eq_a6 hΛ' h

/-- the uncharged statement gives the charged form (the charged form has more hypotheses). -/
theorem theorem_15_3_9_charged_of_statement (H : theorem_15_3_9_statement A) :
    theorem_15_3_9_charged_statement A :=
  fun hX hpara hPU _ f hf hft hS N U hcc Λ hΛ _ hdomU hN1 h hc hfun hh hNh honto =>
    H hX hpara hPU f hf hft hS N U hcc Λ hΛ hdomU hN1 h hc hfun hh hNh honto

/-- **The charged form gives the uncharged statement**: the added hypotheses hold, tame strong
bundle charts by `SEP.exists_isTameChart` and `ChargesBoundary Λ` for every structurable `Λ`
over `∂X` (`IsBoundaryStructurable.chargesBoundary`). -/
theorem theorem_15_3_9_statement_of_charged (H : theorem_15_3_9_charged_statement A) :
    theorem_15_3_9_statement A :=
  fun hX hpara hPU f hf hft hS N U hcc Λ hΛ hdomU hN1 h hc hfun hh hNh honto =>
    H hX hpara hPU (A.exists_isTameChart hX) f hf hft hS N U hcc Λ hΛ hΛ.chargesBoundary hdomU
      hN1 h hc hfun hh hNh honto

/-- **The charged form and the uncharged statement of Theorem 15.3.9 are equivalent.** -/
theorem theorem_15_3_9_charged_iff :
    theorem_15_3_9_charged_statement A ↔ theorem_15_3_9_statement A :=
  ⟨theorem_15_3_9_statement_of_charged, theorem_15_3_9_charged_of_statement⟩

/-- **Step (a) of the proof of Theorem 15.3.9, the cut-off `h₀`** (`lemma_15_3_9_cutoff_hyp`
with its tame strong bundle charts from `SEP.exists_isTameChart`). -/
theorem lemma_15_3_9_cutoff : lemma_15_3_9_cutoff_statement A :=
  fun hX => lemma_15_3_9_cutoff_hyp (A.exists_isTameChart hX) hX

/-- **Proof of Theorem 15.3.9, steps (a)–(e), on the charged Theorem 14.1.9** (`theorem_15_3_9_hyp`
with step (b) unconditional `theorem_14_1_9_charged_a6` and step (a)
`lemma_15_3_9_cutoff_hyp`): only the relative statement (steps (c)–(d)) is assumed. -/
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

/-- **2021 Theorem 15.3.9 (Transversal Extension Theorem), p. 694 (2017: Theorem 15.5)**,
the uncharged statement, from the relative general position step alone (
`theorem_15_3_7_relative_statement`, steps (c)–(d)): `theorem_15_3_9_hyp` with Theorem 14.1.9
(`theorem_14_1_9`) and the cut-off (`lemma_15_3_9_cutoff`) proved. -/
theorem theorem_15_3_9_of_rel (hrel : theorem_15_3_7_relative_statement A) :
    theorem_15_3_9_statement A :=
  theorem_15_3_9_hyp theorem_14_1_9 lemma_15_3_9_cutoff hrel

variable (A) in
/-- **The remaining step**: the relative local families of the proof of Theorem 15.3.9 (steps
(c)–(d), "argue as in Theorem 15.3.7"; `HasLocalGPFamiliesRel` with domain support in
`U ∖ ∂X` and size `h − N(Λ₀)`), under the hypotheses of the relative statement. -/
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

/-- **Theorem 15.3.9 (Transversal Extension Theorem), p. 694, charged form**, from one
remaining step (`relative_local_families_statement`): Theorem 14.1.9 is unconditional
`theorem_14_1_9_charged_a6`, the cutoff is `lemma_15_3_9_cutoff`, the relative parametric step is
`hasParametricGeneralPositionRel`. -/
theorem theorem_15_3_9_charged_of_local_rel (H : relative_local_families_statement A) :
    theorem_15_3_9_charged_statement A :=
  theorem_15_3_9_charged_hyp (theorem_15_3_7_relative_of_local H)

/-- **Theorem 15.3.9, the uncharged statement**, from the one remaining step
(`relative_local_families_statement`). -/
theorem theorem_15_3_9_of_local_families (H : relative_local_families_statement A) :
    theorem_15_3_9_statement A :=
  theorem_15_3_9_statement_of_charged (theorem_15_3_9_charged_of_local_rel H)

/-- **The charged form holds on `ℝⁿ × ℝ⁰ → ℝⁿ`** (no boundary; a witness). -/
theorem theorem_15_3_9_charged_statement_epSEP_zero (n : ℕ) :
    theorem_15_3_9_charged_statement (StrongBundleEquivalenceExamples.epSEP n 0) :=
  theorem_15_3_9_charged_of_statement (theorem_15_3_9_statement_epSEP_zero n)

/-- **The remaining step holds on `ℝⁿ × ℝ⁰ → ℝⁿ`** (fibres `0`; a weak witness, no boundary). -/
theorem relative_local_families_statement_epSEP_zero (n : ℕ) :
    relative_local_families_statement (StrongBundleEquivalenceExamples.epSEP n 0) :=
  fun _ _ _ f _ _ _ _ _ hcc _ _ _ _ Λ₀ _ _ _ _ =>
    hasLocalGPFamiliesRel_epSEP_zero n f Λ₀ hcc.1.isAuxNorm _ _

end SBLocalization

end Polyfold
