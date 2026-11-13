import Polyfold.Chapter15.P3W5GA_Seeds
import Polyfold.Chapter15.P3W5GB_ParametricGP

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3,
**Theorem 15.3.7** (General Position; 2017: Theorem 15.4), pp. 693–698.

# Theorem 15.3.7 with the two pointwise Props only

`theorem_15_3_7_of_pointwise` (`P3W5GA_Seeds`) proves `theorem_15_3_7_statement` from a good system
and, under the hypotheses of the theorem, `HasPointwiseParamOnto`, `HasParamOntoOpen` and
`HasParametricGeneralPosition`. The last is proved under those hypotheses by
`hasParametricGeneralPosition` (`P3W5GB_ParametricGP`). Combining the two:

* **`theorem_15_3_7_of_paramOnto`**: Theorem 15.3.7 (`theorem_15_3_7_statement`) from a good system
  and, under the hypotheses of the theorem, the two Props `HasPointwiseParamOnto` ((15.1) at one
  point with small vectors) and `HasParamOntoOpen` (openness of (15.1) along `S_f`).
* **`theorem_15_3_7_statement_epSEP_zero_of_paramOnto`**: the remaining hypotheses hold together on
  `ℝⁿ × ℝ⁰ → ℝⁿ`.
-/

set_option maxSynthPendingDepth 3

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

variable {A : SEP.{u}}

/-- **Theorem 15.3.7 (`theorem_15_3_7_statement`)** from a good system and, under the hypotheses
of the theorem, `HasPointwiseParamOnto` and `HasParamOntoOpen`; the parametric step
`HasParametricGeneralPosition` is discharged by `hasParametricGeneralPosition`. -/
theorem theorem_15_3_7_of_paramOnto (h𝒰 : Nonempty A.X.GoodSystem)
    (H : A.X.IsTame → A.X.AdmitsBumpFunctionsPointwise →
      ∀ f : A.Obj → A.W, A.E.IsScFredholmSectionFunctor f → A.B.IsScFredholmSectionTame f →
        A.E.HasCompactSolutionSetEp f →
        ∀ (N : A.B.One → ℝ) (U : Set A.Obj), ControlsCompactness A f N U →
          HasPointwiseParamOnto A f N ∧ HasParamOntoOpen A f) :
    theorem_15_3_7_statement A :=
  theorem_15_3_7_of_pointwise h𝒰 fun htame hbump f hf hft hS N U hcc =>
    ⟨(H htame hbump f hf hft hS N U hcc).1, (H htame hbump f hf hft hS N U hcc).2,
      hasParametricGeneralPosition htame hf hft hS hcc⟩

/-- **The hypotheses of `theorem_15_3_7_of_paramOnto` hold together** on `ℝⁿ × ℝ⁰ → ℝⁿ`. -/
theorem theorem_15_3_7_statement_epSEP_zero_of_paramOnto (n : ℕ) :
    theorem_15_3_7_statement (StrongBundleEquivalenceExamples.epSEP n 0) :=
  theorem_15_3_7_of_paramOnto (nonempty_goodSystem_epSEP_zero n)
    fun _ _ f _ _ _ N _ _ => ⟨hasPointwiseParamOnto_epSEP_zero n f N,
      hasParamOntoOpen_epSEP_zero n f⟩

end SBLocalization

end Polyfold
