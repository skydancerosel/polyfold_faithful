import Polyfold
/-! Blind formalization of V5_54 (the text's §5.4.2, Definition 5.36, p. 195).

Text: `(O, C, E)` has the sc-smooth approximation property if for `V ⊆ O` open with
`cl_C(V) ⊆ O`, continuous `f : O → [0, 1]` supported in `V` and `ε > 0` there is an sc-smooth
`g : O → [0, 1]` supported in `V` with `|f − g| ≤ ε`.

Choices:
- This item is a definition.  B says that the project's `M.HasApproxProperty` is the text's notion
  `HasApproxPropertyB M` written below, for every local model `M = (O, C, E)` (the project's
  `LocalModel`; levels of `E` in `Type`).
- "`V ⊆ O` open": open in the topology of `O`, i.e. `V = O ∩ W` for some `W` open in `E₀`.
  `cl_C(V)`: the closure in the subspace `C`, i.e. `cl_E(V) ∩ C` (literal; `C`, a partial quadrant,
  is closed, so this is `cl_E(V)`).
- "continuous `f : O → [0, 1]`": `f : E₀ → ℝ` (total; values off `O` irrelevant), continuous on `O`
  with values in `[0, 1]` on `O`.  "supported in `V`": `supp_O(f) = cl_O{y ∈ O | f(y) ≠ 0}
  = cl_E(O ∩ {f ≠ 0}) ∩ O ⊆ V`; the same for `g`.
- "sc-smooth `g : O → [0, 1]`": the project's `IsScSmoothRetractMap E C O realSc univ univ g`
  (checked with `#print`: `g ∘ r` sc-smooth for every sc-smooth retraction `r` onto `O`; the text's
  notion, which does not depend on `r`) with values in `[0, 1]` on `O`.
- "`|f − g| ≤ ε`": at every point of `O`.  Every `ε > 0`.
- Nothing looks false to me.
-/
namespace RoundTrip.V5_54
open Polyfold

/-- **Definition 5.36**: the sc-smooth approximation property of `(O, C, E)`. -/
def HasApproxPropertyB (M : LocalModel) : Prop :=
  ∀ V : Set (M.E.lvl 0), V ⊆ M.O → (∃ W, IsOpen W ∧ V = M.O ∩ W) → closure V ∩ M.C ⊆ M.O →
    ∀ f : M.E.lvl 0 → ℝ, ContinuousOn f M.O → (∀ y ∈ M.O, f y ∈ Set.Icc (0 : ℝ) 1) →
      closure (M.O ∩ Function.support f) ∩ M.O ⊆ V →
      ∀ ε : ℝ, 0 < ε →
        ∃ g : M.E.lvl 0 → ℝ,
          IsScSmoothRetractMap M.E M.C M.O realSc Set.univ Set.univ g ∧
          (∀ y ∈ M.O, g y ∈ Set.Icc (0 : ℝ) 1) ∧
          closure (M.O ∩ Function.support g) ∩ M.O ⊆ V ∧
          ∀ y ∈ M.O, |f y - g y| ≤ ε

/-- Definition 5.36: the project's sc-smooth approximation property is the text's. -/
def B : Prop :=
  ∀ M : LocalModel, M.HasApproxProperty ↔ HasApproxPropertyB M

end RoundTrip.V5_54
