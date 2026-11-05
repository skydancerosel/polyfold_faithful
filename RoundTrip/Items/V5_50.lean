import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V5_50

/-!
Round trip for V5_50 (Definition 5.31: `C^k`-bump functions).

The listed declarations `Polyfold.HasContDiffBump` and `Polyfold.AdmitsContDiffPartitionsOfUnity`
are both definitions, so `A = True`; the content of the audit is the comparison of the project's
notion with B's, which is B itself, proved outright here (`B_holds`).

`HasContDiffBump V k` is `∃ f, ContDiff ℝ k f ∧ f ≠ 0 ∧ IsBounded (support f)`; B's `HasCkBumpB`
is `∃ f, ContDiff ℝ k f ∧ (∃ x, f x ≠ 0) ∧ ∃ R, tsupport f ⊆ closedBall 0 R`.  The smoothness
clause is literally the same (`k : ℕ∞` cast to `WithTop ℕ∞`), `f ≠ 0 ↔ ∃ x, f x ≠ 0`, and a set
is bounded iff its closure lies in a closed ball around `0`.  The project's definition does not
use completeness (B assumes it; harmless).

B does not mention the second listed definition, `AdmitsContDiffPartitionsOfUnity` (the text's
"`E` admits `C^k` partitions of unity", used before Proposition 5.38); it is not compared.
-/

namespace RoundTrip.V5_50
open Polyfold Set Function

/-- Only definitions are listed: `A = True`. -/
def A : Prop := True

theorem A_holds : A := trivial

/-- The project's `C^k`-bump functions are B's. -/
theorem B_holds : B := by
  intro V _ _ _ k
  constructor
  · rintro ⟨f, hf, hf0, hb⟩
    refine ⟨f, hf, Function.ne_iff.1 hf0, ?_⟩
    exact (Metric.isBounded_iff_subset_closedBall (0 : V)).1 hb.closure
  · rintro ⟨f, hf, ⟨x, hx⟩, R, hR⟩
    refine ⟨f, hf, fun h => hx (congrFun h x), ?_⟩
    exact Metric.isBounded_closedBall.subset (subset_tsupport f |>.trans hR)

theorem A_to_B : A → B := fun _ => B_holds

theorem B_to_A : B → A := fun _ => trivial

#rt_check RoundTrip.V5_50.A_to_B []
#rt_check RoundTrip.V5_50.B_to_A []
#rt_overlap RoundTrip.V5_50.B_to_A []
#rt_overlap RoundTrip.V5_50.A_to_B []

end RoundTrip.V5_50
