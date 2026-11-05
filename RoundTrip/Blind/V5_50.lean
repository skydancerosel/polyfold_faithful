import Polyfold
/-! Blind formalization of V5_50 (the text's §5.4.2, Definition 5.31, p. 193).

Text: a Banach space `E` admits a `C^k`-bump function if some `C^k` function `f : E → ℝ`, not
identically zero, has bounded support (`k ∈ {0, 1, …} ∪ {∞}`).

Choices:
- This item is a definition.  B says that the project's `HasContDiffBump V k` is the text's notion
  `HasCkBumpB V k` written below, for every real Banach space `V : Type` (universe 0, as asked;
  the text's `E` is a Banach space, so completeness is assumed) and every `k`.
- `k ∈ {0, 1, …} ∪ {∞}`: `k : ℕ∞`, `⊤` being `∞`; "`C^k`" is Mathlib's `ContDiff ℝ k` with `k`
  cast to `WithTop ℕ∞` (so `k = ⊤` is `C^∞`, not analytic).
- "not identically zero": `∃ x, f x ≠ 0`.  "bounded support": the support `cl{f ≠ 0}` lies in some
  closed ball around `0`.
- Nothing looks false to me.
-/
namespace RoundTrip.V5_50
open Polyfold

/-- **Definition 5.31**: `V` admits a `C^k`-bump function: a `C^k` map `f : V → ℝ`, not
identically zero, with bounded support. -/
def HasCkBumpB (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (k : ℕ∞) : Prop :=
  ∃ f : V → ℝ, ContDiff ℝ (k : WithTop ℕ∞) f ∧ (∃ x, f x ≠ 0) ∧
    ∃ R : ℝ, tsupport f ⊆ Metric.closedBall (0 : V) R

/-- Definition 5.31: the project's `C^k`-bump functions are the text's. -/
def B : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (k : ℕ∞),
    HasContDiffBump V k ↔ HasCkBumpB V k

end RoundTrip.V5_50
