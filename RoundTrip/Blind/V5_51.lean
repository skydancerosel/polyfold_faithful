import Polyfold
/-! Blind formalization of V5_51 (the text's §5.4.2, Definition 5.33, p. 194).

Text: `(O, C, E)` has the sc-smooth bump function property if for every `x ∈ O` and open
`U(x) ⊆ O` with `cl_E(U(x)) ⊆ O` there is an sc-smooth `f : O → ℝ` with `f ≠ 0` and
`supp(f) ⊆ U(x)`.

Choices:
- This item is a definition.  B says that the project's `M.HasBumpProperty` (the only project
  notion for Definition 5.33) is the text's notion `HasBumpPropertyB M` written below, for every
  local model `M = (O, C, E)` (the project's `LocalModel`: an sc-Banach space `E`, levels in `Type`,
  and an sc-smooth retract `O` in the partial quadrant `C`).
- "open `U(x) ⊆ O`": `U ⊆ O` open in the topology of `O`, i.e. `U = O ∩ W` for some `W` open in
  `E₀`, with `x ∈ U`.  `cl_E(U(x))`: the closure in `E = E₀`.
- "sc-smooth `f : O → ℝ`": the project's `IsScSmoothRetractMap E C O realSc univ univ f` (checked
  with `#print`: `f` maps `O` into `ℝ` and `f ∘ r` is sc-smooth on `U_r` for every sc-smooth
  retraction `r : U_r → U_r` onto `O`; by the text this does not depend on `r`), `f` a total map
  `E₀ → ℝ` whose values off `O` are irrelevant.
- "`f ≠ 0`": read LITERALLY, `f` is not the zero function on `O` (`∃ y ∈ O, f y ≠ 0`), the plain
  meaning of `f ≠ 0` for a function and the reading Definition 5.29 spells out ("not identically
  zero"); the same reading as `RoundTrip/Blind/V5_52.lean`.  The project's `HasBumpProperty`
  reads it as `f(x) ≠ 0` (its docstring, and `#print`): a stronger property.  I believe the
  literal reading is the text's, so B (an equivalence) may well FAIL; `BPointwise` below (not the
  item) records the equivalence under the pointwise reading.
- "`supp(f)`": the support in `O`, `cl_O{y ∈ O | f(y) ≠ 0} = cl_E(O ∩ {f ≠ 0}) ∩ O`.
-/
namespace RoundTrip.V5_51
open Polyfold

/-- **Definition 5.33** (literal): for every `x ∈ O` and every open `U ∋ x` of `O` with
`cl_E(U) ⊆ O` there is an sc-smooth `f : O → ℝ`, not identically zero on `O`, with
`supp_O(f) ⊆ U`. -/
def HasBumpPropertyB (M : LocalModel) : Prop :=
  ∀ x ∈ M.O, ∀ U : Set (M.E.lvl 0), U ⊆ M.O → x ∈ U → (∃ W, IsOpen W ∧ U = M.O ∩ W) →
    closure U ⊆ M.O →
      ∃ f : M.E.lvl 0 → ℝ,
        IsScSmoothRetractMap M.E M.C M.O realSc Set.univ Set.univ f ∧
        (∃ y ∈ M.O, f y ≠ 0) ∧ closure (M.O ∩ Function.support f) ∩ M.O ⊆ U

/-- Not the item: Definition 5.33 with `f ≠ 0` read as `f(x) ≠ 0`. -/
def HasBumpPropertyPointB (M : LocalModel) : Prop :=
  ∀ x ∈ M.O, ∀ U : Set (M.E.lvl 0), U ⊆ M.O → x ∈ U → (∃ W, IsOpen W ∧ U = M.O ∩ W) →
    closure U ⊆ M.O →
      ∃ f : M.E.lvl 0 → ℝ,
        IsScSmoothRetractMap M.E M.C M.O realSc Set.univ Set.univ f ∧
        f x ≠ 0 ∧ closure (M.O ∩ Function.support f) ∩ M.O ⊆ U

/-- Definition 5.33: the project's sc-smooth bump function property of a local model is the
text's (literal reading). -/
def B : Prop :=
  ∀ M : LocalModel, M.HasBumpProperty ↔ HasBumpPropertyB M

/-- Not the item: the project's notion is the pointwise reading. -/
def BPointwise : Prop :=
  ∀ M : LocalModel, M.HasBumpProperty ↔ HasBumpPropertyPointB M

end RoundTrip.V5_51
