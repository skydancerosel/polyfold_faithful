import Polyfold
/-! Blind formalization of V9_35 (the text's Part II, §9.3, Lemma 9.3.7, p. 426 of the Springer
2021 book; new in the 2021 edition): equal tangent spaces have equal degeneracy.

Text: if `Y` is a tame M-polyfold, `M₁`, `M₂` submanifolds of the same dimension with tame
induced structures and `y ∈ M₁ ∩ M₂`, then `T_yM₁ = T_yM₂` implies `d_{M₁}(y) = d_{M₂}(y)`.

Choices:
- Setting: `Z : Type` (universe 0) Hausdorff, paracompact, `P : MPolyfold Z` (the project's
  M-polyfold); "tame": the project's `P.IsTame` (Definition 2.37, `#print`ed: an equivalent atlas
  of tame retracts).
- "submanifolds of the same dimension": smooth finite-dimensional submanifolds which are both
  `n`-dimensional for one `n` (the project's `IsSubmanifoldOfDim`, `#print`ed: a smooth
  submanifold, Definition 4.13, with `dim T_aM = n` at every `a ∈ M`, read in a chart; compared
  with the text in `RoundTrip/Blind/V9_2.lean`).
- "with tame induced structures": the project's `HasTameInducedStructure` (`#print`ed: `M` is a
  sub-M-polyfold whose induced structure is tame).
- `T_yM`: the project's `submanifoldTangent M y` (`#print`ed: the tangent vectors over `y` fixed
  by the tangent map of an sc⁺-retraction onto `M` near `y`, i.e. `Tr(y)(T_yX)`, V9_12).
- `d_M(y)`: my `dMB`, the degeneracy index of `y` in the induced structure (the project's
  `subDegIndex`, `#print`ed: `(subPolyfold hA).degIndex`), with a junk value `0` when `M` is not
  a sub-M-polyfold or `y ∉ M` (not used under the hypotheses, assuming smooth submanifolds are
  sub-M-polyfolds, as `HasTameInducedStructure` asserts anyway).
- Nothing looks false to me.
-/
namespace RoundTrip.V9_35
open Polyfold

open Classical in
/-- `d_M(y)`: the degeneracy index of `y` for the structure induced on the sub-M-polyfold `M`
(`0` if `M` is not a sub-M-polyfold or `y ∉ M`). -/
noncomputable def dMB {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]
    (P : MPolyfold Z) (M : Set Z) (y : Z) : ℕ :=
  if h : P.IsSubMPolyfold M ∧ y ∈ M then P.subDegIndex h.1 ⟨y, h.2⟩ else 0

/-- **Lemma 9.3.7**: in a tame M-polyfold, two submanifolds of the same dimension with tame
induced structures and the same tangent space at a common point `y` have the same degeneracy
index at `y`. -/
def B : Prop :=
  ∀ (Z : Type) [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] (P : MPolyfold Z),
    P.IsTame → ∀ (M₁ M₂ : Set Z) (n : ℕ),
      P.IsSubmanifoldOfDim M₁ n → P.IsSubmanifoldOfDim M₂ n →
      P.HasTameInducedStructure M₁ → P.HasTameInducedStructure M₂ →
      ∀ y ∈ M₁ ∩ M₂, P.submanifoldTangent M₁ y = P.submanifoldTangent M₂ y →
        dMB P M₁ y = dMB P M₂ y

end RoundTrip.V9_35
