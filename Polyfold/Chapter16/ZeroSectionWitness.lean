import Polyfold.Chapter16.ZeroSection
import Polyfold.Chapter16.IndexZeroTwoModels

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, Chapter 16,
§16.3 (p. 728, before Definition 16.3.18): **a witness for the zero section** `z ↦ 0_z` as an
sc⁺-section (`StrongPolyfoldBundle.zeroSection`, `Chapter16/ZeroSection.lean`).

## What is formalized

* `TrivialBundle.zeroSection_epPolyfoldBundle`: the zero section of the strong polyfold bundle
  `|ℝ × ℝ| → |ℝ|` (`epPolyfoldBundle`, Definition 16.3.4), an `ScPlusSection`.
* `toFun_zeroSection_epPolyfoldBundle`: its function is `z ↦ 0_z`;
  `solutionSet_zeroSection_epPolyfoldBundle`: its solution set is all of `|ℝ|`, a nonempty set.
-/

set_option maxSynthPendingDepth 3

open Set

noncomputable section

namespace Polyfold

namespace TrivialBundle

open StrongPolyfoldBundle StrongBundleEquivalenceExamples

/-- **Witness**: the zero section of `|ℝ × ℝ| → |ℝ|` as an sc⁺-section (Definitions 16.3.18,
16.3.19). -/
def zeroSection_epPolyfoldBundle : ScPlusSection epPolyfoldBundle :=
  zeroPlusSection epPolyfoldBundle

theorem toFun_zeroSection_epPolyfoldBundle :
    (zeroSection_epPolyfoldBundle.1).toFun = epPolyfoldBundle.zeroAt := rfl

theorem isScPlus_zeroSection_epPolyfoldBundle : (zeroSection_epPolyfoldBundle.1).IsScPlus :=
  zeroSection_epPolyfoldBundle.2

/-- The solution set of the zero section is the whole (nonempty) base `|ℝ|`. -/
theorem solutionSet_zeroSection_epPolyfoldBundle :
    (zeroSection_epPolyfoldBundle.1).solutionSet = univ ∧
      (zeroSection_epPolyfoldBundle.1).solutionSet.Nonempty := by
  have h : (zeroSection_epPolyfoldBundle.1).solutionSet = univ :=
    solutionSet_zeroSection epPolyfoldBundle
  exact ⟨h, ⟨(epSEP 1 1).X.π (0 : Fin 1 → ℝ), by rw [h]; trivial⟩⟩

end TrivialBundle

end Polyfold
