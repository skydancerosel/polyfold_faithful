import Polyfold
/-! Blind formalization of V5_52 (the text's §5.4.2, Theorem 5.34, p. 194).

Text ("Clearly"): `X` admits sc-smooth bump functions iff it admits an sc-smooth atlas whose local
models have the sc-smooth bump function property.

Choices:
- Setting: `X : Type` (universe 0, as asked), Hausdorff paracompact, with an M-polyfold structure
  `PX : MPolyfold X` (Definition 2.13).  B is the equivalence for every such `(X, PX)`.
- "`X` admits sc-smooth bump functions" (Definition 5.29, §5.4.2, where the theorem sits: for
  every `x` and open `U(x)` an sc-smooth `f : X → ℝ` "not identically zero" with
  `supp(f) ⊆ U(x)`): the project's `PX.AdmitsBumpFunctionsWeak` (checked with `#print`: `f`
  sc-smooth into `ℝ`, `f ≠ 0` as a function, `tsupport f ⊆ U`).
- "sc-smooth bump function property" of a local model (Definition 5.33: for every `x ∈ O` and open
  `U(x) ⊆ O` with `cl_E(U(x)) ⊆ O` an sc-smooth `f : O → ℝ` with `f ≠ 0` and `supp(f) ⊆ U(x)`):
  `f ≠ 0` read literally, as in Definition 5.29, i.e. `f` not identically zero on `O`.  The
  project's `LocalModel.HasBumpProperty` reads `f ≠ 0` as `f(x) ≠ 0` (its docstring), so I do NOT
  use it; `HasBumpPropertyWeak` below is the project's definition (checked with `#print`: `U(x) =
  O ∩ W` with `W` open in `E_0`, `x ∈ W`, `closure (O ∩ W) ⊆ O` in `E_0`; `f : E_0 → ℝ` sc-smooth
  on the retract `O`, `IsScSmoothRetractMap … realSc univ univ`; `supp(f)` the closure in `O` of
  `{f ≠ 0}`, `closure (O ∩ support f) ∩ O ⊆ W`) with `f(x) ≠ 0` replaced by `∃ y ∈ O, f(y) ≠ 0`.
  Both sides of B thus use the same ("not identically zero") reading; mixing the two readings
  would change the claim.
- "admits an sc-smooth atlas": an atlas `A` of the given M-polyfold structure, i.e. equivalent to
  `PX.atlas` (`MAtlas.Equiv`, Definition 2.12: the union is an atlas), all of whose charts have a
  local model with the property.
- `BStrong` (NOT the item, only an aid): the same equivalence with the `f(x) ≠ 0` reading on both
  sides (the project's `AdmitsBumpFunctions` and `HasBumpProperty`).
- Nothing looks false to me.
-/
namespace RoundTrip.V5_52
open Polyfold

/-- Definition 5.33, literal reading: the local model `(O, C, E)` has the sc-smooth bump function
property: for every `x ∈ O` and open `U(x) = O ∩ W ∋ x` with `cl_E(U(x)) ⊆ O` there is an
sc-smooth `f : O → ℝ`, not identically zero on `O`, with `supp_O(f) ⊆ U(x)`. -/
def HasBumpPropertyWeak (M : LocalModel) : Prop :=
  ∀ x ∈ M.O, ∀ W : Set (M.E.lvl 0), IsOpen W → x ∈ W → closure (M.O ∩ W) ⊆ M.O →
    ∃ f : M.E.lvl 0 → ℝ,
      IsScSmoothRetractMap M.E M.C M.O realSc Set.univ Set.univ f ∧
      (∃ y ∈ M.O, f y ≠ 0) ∧ closure (M.O ∩ Function.support f) ∩ M.O ⊆ W

/-- Theorem 5.34: an M-polyfold admits sc-smooth bump functions iff it has an (equivalent)
sc-smooth atlas whose local models have the sc-smooth bump function property. -/
def B : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X),
    PX.AdmitsBumpFunctionsWeak ↔
      ∃ A : MAtlas X, A.Equiv PX.atlas ∧ ∀ φ ∈ A.charts, HasBumpPropertyWeak φ.model

/-- Not the item: the same equivalence with the reading `f(x) ≠ 0` on both sides. -/
def BStrong : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X),
    PX.AdmitsBumpFunctions ↔
      ∃ A : MAtlas X, A.Equiv PX.atlas ∧ ∀ φ ∈ A.charts, φ.model.HasBumpProperty

end RoundTrip.V5_52
