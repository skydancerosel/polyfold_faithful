import Polyfold.Chapter16.CanonicalModelTransfer
import Polyfold.Chapter15.CanonicalOrientationPullback

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §16.6 (p. 739), with
**Theorem 15.4.1** and **Definition 15.4.2** (pp. 701–702).

# The canonical orientation on the middle bundle of a correspondence

For a correspondence `W₁ ←Φ W'' →Ψ W₂` between two orientation representatives and a
canonically oriented regular perturbation `(Λ, T̂)` in the model of `o`, the pull-back `ϕ^* T̂`
is canonical for `(Λ ∘ Φ, Φ^* o)` on `W''` (`IsCanonicalFor.pullSection`).  So
**`Correspondence.middleCanonical`**: every correspondence satisfies `MiddleCanonical`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

noncomputable section

namespace Polyfold

universe u

open SBLocalization

namespace StrongPolyfoldBundle.OrientationRep.Correspondence

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {c : StrongPolyfoldBundle p} {s : FredholmSection c} {o o' : OrientationRep s}

/-- **The middle bundle carries the pulled canonical orientation** (Theorem 15.4.1, Definition
15.4.2, §16.6 p. 739): for every canonically oriented regular perturbation `(Λ, T̂)` of the model
of `o`, `ϕ^* T̂` is canonical on `W''` for `(Λ ∘ Φ, Φ^* o)`, of dimension `m + 1`. -/
theorem middleCanonical (C : Correspondence o o') (m : ℕ) : C.MiddleCanonical m :=
  fun _ hP => ⟨m + 1, _,
    IsCanonicalFor.pullSection C.D.hΦ C.hF'' o.hF C.hpb₁ C.hsec'' o.hsec hP⟩

end StrongPolyfoldBundle.OrientationRep.Correspondence

end Polyfold
